# -*- coding: utf-8 -*-
"""Bambu Lab A1 看板 —— 小D 做的

数据来源（全部走局域网，不经过拓竹云端）:
  * MQTT over TLS  端口 8883, 用户名 bblp, 密码 = 打印机的访问码
       - device/<序列号>/report   收状态
       - device/<序列号>/request  下命令
       注意: 订阅只能用具体主题, 用 '#' 通配符会被拒(实测收不到任何消息)
  * 摄像头          端口 6000, TLS 握手后发 64 字节认证包, 之后连续收 1536x1080 JPEG
  * 文件            端口 990, implicit FTPS (不是标准的 AUTH TLS)
       里面有: /timelapse 延时摄影 /ipcam 全程录像 /logger 日志(加密)
               /recorder 黑匣子 /cache 切片文件 /image 缩略图

实测拿不到的 (别浪费时间):
  * mc_print 实时日志 —— 这台 A1 固件不往局域网推, 打印中 22 秒 0 条
  * /logger 里的日志是加密二进制, 且 FTP 不支持 REST 断点续传
  * 摄像头只有约 0.46 帧/秒, A1 没有 RTSP
  * 灯光的「闪」模式 —— 发过去打印机回 result=success, 但灯不动、状态也不变
  * **打印控制按钮按不动 —— 真正的原因(已查实)** —— 固件开了「授权校验」(新的授权控制系统)。
    带顶层 "print" 的命令必须带一个 header 信封, 里面是拿**拓竹 Studio 的私有密钥**做的
    RSA-SHA256 签名; 没签名的会被拒, 报的就是 HMS_0500-0500-0001-0007
    「MQTT 命令校验失败，请更新 Studio 或 Handy」。灯(system.ledctrl)不在校验范围, 所以能用。
    依据: https://wiki.bambulab.com/zh/x1/troubleshooting/hmscode/0500_0500_0001_0007
          https://raw.githubusercontent.com/ClusterM/open-bamboo-networking/master/research/10.04-mqtt-signing.md
    对得上的旁证: 我们抓到的 print.flag3 = 221855, 它的第 16 位 = 1,
    而那份文档说「启用了新授权系统的打印机会把 flag3 第 16 位置 1」。
    ⚠️ 所以之前我猜的「切局域网模式就行」是**错的** —— 签名要求和局域网/云端无关。
    正规出路只有两条: ① 打印机上打开「开发者模式」(开了签名可以不签);
    ② 用 Bambu Studio / 手机 App 这些有签名的官方客户端。
    **不要去抠拓竹 Studio 里的私有密钥来签名** —— 那是破人家的保护, 不做。
  * ⚠️ 命令一律用 QoS 0。文档说 pause/stop 要用 QoS 1, 实测改成 QoS 1 之后
    连原本能用的灯光都不响应了 —— broker 大概是收到 QoS 1 就把会话断开。
"""
import datetime
import ftplib
import http.server
import io
import hashlib
import json
import math
import os
import queue
import re
import socket
import ssl
import struct
import sys
import threading
import time
import traceback
import urllib.parse
import xml.etree.ElementTree as ET
import zipfile
from collections import deque

import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk

try:
    import paho.mqtt.client as mqtt
except ImportError:
    mqtt = None

try:
    from PIL import Image, ImageDraw, ImageTk
except ImportError:
    Image = None
    ImageDraw = None
    ImageTk = None

if getattr(sys, "frozen", False):          # 打包成 exe 之后：配置/截图存在 exe 旁边
    HERE = os.path.dirname(os.path.abspath(sys.executable))
else:
    HERE = os.path.dirname(os.path.abspath(__file__))
CONF_JSON = os.path.join(HERE, "bambu_dash.json")
LOG_FILE = os.path.join(HERE, "bambu_dash.log")
SHOT_DIR = os.path.join(HERE, "bambu_截图")
DL_ROOT = os.path.join(HERE, "打印机下载")
STUDIO_CONF = os.path.join(os.environ.get("APPDATA", ""), "BambuStudio", "BambuStudio.conf")
WEB_PASS_FILE = os.path.join(os.path.expanduser("~"), "Desktop", "Bambu看板访问码.txt")


def web_pass_read():
    """读桌面上的访问码文件（每次请求都重读，所以改完立刻生效）；没有就生成一个。"""
    try:
        with io.open(WEB_PASS_FILE, encoding="utf-8") as fh:
            code = fh.read().strip()
        if code:
            return code
    except (IOError, OSError):
        pass
    code = "%06d" % (int.from_bytes(os.urandom(3), "big") % 1000000)
    try:
        with io.open(WEB_PASS_FILE, "w", encoding="utf-8") as fh:
            fh.write(code + "\n")
        log("访问码文件已生成: " + WEB_PASS_FILE)
    except (IOError, OSError):
        log("!! 写不了访问码文件: " + WEB_PASS_FILE)
    return code


CAM_W, CAM_H = 480, 338
CHART_W, CHART_H = 430, 150
CHART_POINTS = 450      # 2 秒一个点, 450 个 = 最近 15 分钟
SAMPLE_SEC = 2.0
THUMB_W, THUMB_H = 384, 270

BG = "#12161c"
CARD = "#1b2129"
CARD2 = "#232b35"
FG = "#e8edf2"
DIM = "#8b98a8"
ACC = "#3ea6ff"
HOT = "#ff6b4a"
COOL = "#4ad6c0"
OK = "#4ad07a"
WARN = "#ffc14a"
BAD = "#ff5c5c"
FONT = "Microsoft YaHei UI"
MONO = "Consolas"

STATE_CN = {"IDLE": "空闲", "RUNNING": "打印中", "PAUSE": "已暂停", "FINISH": "已完成",
            "FAILED": "失败", "PREPARE": "准备中", "SLICING": "切片中", "UNKNOWN": "未知"}
SPEED_CN = {1: "静音", 2: "标准", 3: "运动", 4: "狂暴"}

# 打印阶段（打印机报的 stg_cur）。
# 代码来自 pybambu（ha-bambulab 用的那个库）的 const.py -> CURRENT_STAGE_IDS，
# 不是拓竹官方文档，但它是社区通用的一份，值 0~35 和 -1/255 都对得上。
STAGE_CN = {
    0: "打印中", 1: "自动调平（热床调平）", 2: "热床预热", 3: "振动补偿",
    4: "换料中", 5: "暂停（M400）", 6: "缺料暂停", 7: "加热热端",
    8: "挤出校准", 9: "扫描热床", 10: "检查首层", 11: "识别热床类型",
    12: "校准激光雷达", 13: "回零", 14: "清理喷嘴", 15: "检查挤出机温度",
    16: "用户暂停", 17: "前盖掉落暂停", 18: "校准激光雷达", 19: "校准流量",
    20: "喷嘴温度异常暂停", 21: "热床温度异常暂停", 22: "退料中", 23: "丢步暂停",
    24: "进料中", 25: "电机降噪校准", 26: "AMS 掉线暂停", 27: "热端风扇转速低暂停",
    28: "腔温控制异常暂停", 29: "腔体冷却", 30: "用户 G-code 暂停",
    31: "电机降噪展示", 32: "检测到喷嘴裹料暂停", 33: "切刀异常暂停",
    34: "首层异常暂停", 35: "喷嘴堵塞暂停", -1: "空闲", 255: "空闲",
}


def stage_name(code):
    if code is None:
        return ""
    try:
        n = int(code)
    except (TypeError, ValueError):
        return ""
    return STAGE_CN.get(n, "阶段 %d" % n)

# 降温估计用的常数
COOL_ENV = 25.0                               # 环境温度，算降温曲线用
COOL_GOAL = {"nozzle": 50.0, "bed": 40.0}     # 凉到这个温度就算能碰了
TAU_DEFAULT = {"nozzle": 90.0, "bed": 480.0}  # 秒。还没测到完整降温过程时先用的粗估常数
TGT_HOT = "#a3502f"                           # 目标温度虚线（喷嘴）
TGT_COOL = "#2e7f76"                          # 目标温度虚线（热床）

# 打印机内部目录 -> 电脑上的文件夹名
REMOTE_DIRS = [
    ("/timelapse", "延时摄影", "打印延时摄影（每打一盘一段）"),
    ("/ipcam", "录像", "打印全程录像（最占地方）"),
    ("/cache", "切片缓存", "打印过的模型和 gcode"),
    ("/image", "图片", "每盘的模型缩略图"),
    ("/logger", "日志", "打印机运行日志（加密的，看不懂）"),
    ("/recorder", "黑匣子", "运行数据 bin"),
    ("/", "根目录", "打印机根目录"),
]

# 给平板看的网页（电脑上的看板跑着的时候，平板开 http://电脑IP:8787）
WEB_PORT = 8787
# ⚠️ 必须是原始字符串 r""" —— 里面 JS 有 \n 和 \.avi，普通字符串会被 Python 吃掉
WEB_HTML = r"""<!doctype html>
<html lang="zh-CN"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Bambu 看板</title>
<style>
:root{color-scheme:dark}
*{box-sizing:border-box}
body{margin:0;background:#12161c;color:#e8edf2;
     font-family:system-ui,"Microsoft YaHei",sans-serif;-webkit-text-size-adjust:100%}
.wrap{max-width:820px;margin:0 auto;padding:12px}
.card{background:#1b2129;border-radius:14px;padding:14px;margin-bottom:12px}
h1{font-size:15px;margin:0 0 8px;color:#3ea6ff;font-weight:600}
.big{font-size:32px;font-weight:700;line-height:1.15}
.bar{height:14px;background:#232b35;border-radius:7px;overflow:hidden;margin:10px 0}
.bar>i{display:block;height:100%;background:#3ea6ff;width:0;transition:width .4s}
.row{display:flex;gap:20px;flex-wrap:wrap}
.k{color:#8b98a8;font-size:12px;margin-bottom:2px}
.v{font-size:19px;font-weight:600}
img{width:100%;border-radius:10px;background:#0a0d11;display:block;min-height:120px}
button{background:#2a3341;color:#e8edf2;border:0;border-radius:9px;
       padding:11px 18px;font-size:15px;margin:0 8px 8px 0}
.tabs{display:flex;flex-wrap:wrap;gap:8px;margin:4px 0 12px}
.tabbtn{background:#1b2129;color:#8b98a8;padding:9px 14px;font-size:14px;margin:0}
.tabbtn.on{background:#2a3341;color:#3ea6ff}
.mono{font-family:ui-monospace,Consolas,monospace;font-size:12px;line-height:1.5;
      white-space:pre-wrap;word-break:break-all;color:#c7d2dd;margin:6px 0 0;
      max-height:52vh;overflow:auto}
canvas{width:100%;height:170px;display:block}
.dim{color:#8b98a8;font-size:12px;line-height:1.6}
html,body{max-width:100%;overflow-x:hidden}
.dim,.v,.k,h1,.big{overflow-wrap:anywhere;word-break:break-word}
.tabs{overflow-x:auto}
/* 温度和画面并排：手机上也要挨在一起，宽屏再上下摊开 */
.pair{display:flex;gap:12px;align-items:flex-start}
.pairleft{flex:1 1 58%;min-width:0}
.pairright{flex:1 1 42%;min-width:0}
@media (min-width:760px){
  .pair{flex-wrap:wrap}
  .pairleft{flex:1 1 100%}
  .pairright{flex:1 1 100%}
}
@media (max-width:520px){
  .big{font-size:27px}
  .v{font-size:16px}
  .row{gap:14px}
  img{min-height:0}
  .wrap{padding:9px}
}
</style></head><body><div class="wrap">

<div class="card">
  <h1 id="task">Bambu Lab A1</h1>
  <div class="big" id="state">正在连接…</div>
  <div class="k" id="stage" style="margin-top:2px"></div>
  <div class="bar"><i id="pb"></i></div>
  <div class="row">
    <div><div class="k">进度</div><div class="v" id="pct">—</div></div>
    <div><div class="k">剩余</div><div class="v" id="left">—</div></div>
    <div><div class="k">预计完成</div><div class="v" id="eta">—</div></div>
    <div><div class="k">当前层</div><div class="v" id="layer">—</div></div>
  </div>
  <div class="dim" id="file" style="margin-top:8px"></div>
</div>

<div class="card">
  <h1>这一层的盘面图</h1>
  <img id="lmap" style="width:100%;max-width:300px;background:#12161c;margin:0 auto">
  <div class="dim" id="lmapinfo" style="margin-top:8px">等开始打印后会自动算出来</div>
  <div class="dim">左下角是原点 (0,0)，X 往右、Y 往后　青色=这一层要挤出的地方　橙框=范围</div>
</div>

<div class="card">
  <h1>温度曲线</h1>
  <canvas id="chart" height="170"></canvas>
  <div class="dim" style="margin-bottom:12px">红=喷嘴　青=热床　虚线=目标　（最近 15 分钟，每 3 秒刷新）</div>
  <div class="pair">
    <div class="pairleft">
      <div class="row">
        <div><div class="k">喷嘴</div><div class="v" id="nz">—</div></div>
        <div><div class="k">热床</div><div class="v" id="bd">—</div></div>
        <div><div class="k">腔温</div><div class="v" id="ch">—</div></div>
      </div>
      <div class="dim" id="cool" style="margin-top:8px"></div>
    </div>
    <div class="pairright">
      <img id="cam" alt="">
      <div class="dim" id="camn" style="margin-top:6px"></div>
      <div class="dim" id="cmisc"></div>
      <img id="camannot" style="margin-top:8px" alt="">
      <div class="dim">↑ 识别画面：红线=盘子前沿（推前后）　黄框=喷头标（推左右）</div>
    </div>
  </div>
</div>

<div class="card">
  <h1>其它</h1>
  <div class="dim" id="misc"></div>
  <div style="margin-top:12px">
    <button onclick="light(1)">开灯</button>
    <button onclick="light(0)">关灯</button>
  </div>
</div>

<div class="tabs">
  <button class="tabbtn" data-t="hist" onclick="show('hist')">打印历史</button>
  <button class="tabbtn" data-t="events" onclick="show('events')">事件流水</button>
  <button class="tabbtn" data-t="ctrl" onclick="show('ctrl')">控制</button>
  <button class="tabbtn" data-t="raw" onclick="show('raw')">全部字段</button>
</div>

<div class="page" id="p_hist" style="display:none">
  <div class="card">
    <h1>打印历史（延时摄影）</h1>
    <button onclick="loadHist(1)">重新读取</button>
    <img id="hthumb" style="margin-top:10px;display:none">
    <div id="hist" class="dim" style="margin-top:10px"></div>
  </div>
</div>

<div class="page" id="p_events" style="display:none">
  <div class="card">
    <h1>事件流水</h1>
    <pre id="events" class="mono"></pre>
  </div>
</div>

<div class="page" id="p_ctrl" style="display:none">
  <div class="card">
    <h1>控制</h1>
    <div class="dim" style="margin-bottom:10px">注意：打印机固件对 print 类命令要签名校验，
      没签名的会被拒绝（只有灯能控制）。回执里能看到打印机怎么回。</div>
    <button onclick="cmd('c=pause')">暂停</button>
    <button onclick="cmd('c=resume')">继续</button>
    <button onclick="cmd('c=stop')">停止</button>
    <div style="margin-top:10px">
      <button onclick="cmd('c=speed&v=1')">静音</button>
      <button onclick="cmd('c=speed&v=2')">标准</button>
      <button onclick="cmd('c=speed&v=3')">运动</button>
      <button onclick="cmd('c=speed&v=4')">狂暴</button>
    </div>
    <div class="k" style="margin-top:12px">指令回执</div>
    <pre id="reply" class="mono"></pre>
  </div>
</div>

<div class="page" id="p_raw" style="display:none">
  <div class="card">
    <h1>打印机报上来的全部字段</h1>
    <pre id="raw" class="mono"></pre>
  </div>
</div>

</div>

<div style="margin:14px 0;padding:10px 12px;border:1px solid #39434f;border-radius:8px">
  <div style="font-weight:600;margin-bottom:8px">四角标定（把喷嘴开到盘子的角上，再点对应的按钮）</div>
  <button onclick="cal('lf')">喷嘴在盘左前</button>
  <button onclick="cal('lb')">喷嘴在盘左后</button>
  <button onclick="cal('rf')">喷嘴在盘右前</button>
  <button onclick="cal('rb')">喷嘴在盘右后</button>
  <div id="calinfo" style="color:#8b93a0;margin-top:8px">点一下就会记下喷嘴现在的位置</div>
  <div id="posinfo" style="color:#c9d1d9;margin-top:6px">喷头估算：还没抓到标记</div>
  <div style="color:#e0a33e;margin-top:4px">⚠️ 红点位置是<b>纯靠画面数据估算</b>的（贴纸比喷嘴高几厘米，有视差），可能不准，只当参考</div>
</div>

<div id="login" style="display:none;position:fixed;left:0;top:0;right:0;bottom:0;z-index:200;background:rgba(8,11,15,.94)">
  <div style="max-width:340px;margin:20vh auto;padding:20px;border:1px solid #39434f;border-radius:12px;background:#161b22;text-align:center;color:#e6edf3">
    <div style="font-weight:700;font-size:17px;margin-bottom:10px">请输入访问码</div>
    <div style="font-size:12px;color:#8b93a0;margin-bottom:12px;line-height:1.6">访问码在<b>电脑桌面</b>的「Bambu看板访问码.txt」里<br>改了那个文件，这里重新输一次就行</div>
    <input id="logincode" type="password" inputmode="numeric" style="width:100%;box-sizing:border-box;padding:10px;border-radius:8px;border:1px solid #39434f;background:#0d1117;color:#e6edf3;text-align:center;font-size:19px;letter-spacing:2px">
    <button onclick="doLogin()" style="margin-top:12px;width:100%;padding:10px;font-size:15px">进去</button>
    <div id="loginmsg" style="color:#ff6b6b;font-size:12px;margin-top:10px;min-height:16px"></div>
  </div>
</div>

<div style="margin:14px 0;padding:10px 12px;border:1px solid #39434f;border-radius:8px">
  <div style="font-weight:600;margin-bottom:6px">仪表盘（温度 / 风扇，黄刻度 = 目标值）</div>
  <div id="gauges" style="display:flex;flex-wrap:wrap;gap:4px;justify-content:space-around">等数据…</div>
</div>

<div style="margin:14px 0;padding:10px 12px;border:1px solid #39434f;border-radius:8px">
  <div style="font-weight:600;margin-bottom:8px">全部状态（实时，绿=正常、橙=要注意、红=有问题）</div>
  <div id="statuslist" style="font-size:13px;line-height:1.85">等第一份状态…</div>
</div>

<div id="toast" style="display:none;position:fixed;left:50%;top:10px;transform:translateX(-50%);max-width:92%;z-index:99;padding:10px 16px;border-radius:10px;background:#1b2027;border:2px solid #4ea1ff;color:#e6edf3;box-shadow:0 6px 20px rgba(0,0,0,.55)">
  <div id="toast_t" style="font-weight:700;font-size:15px"></div>
  <div id="toast_x" style="font-size:13px;opacity:.85;margin-top:3px"></div>
</div>

<script>
async function tick(){
  try{
    const resp = await fetch('/api/state',{cache:'no-store'});
    if (resp.status === 401){ showLogin(); return; }
    const s = await resp.json();
    task.textContent = s.task || 'Bambu Lab A1';
    state.textContent = s.state;
    stage.textContent = s.stage ? ('阶段：' + s.stage) : '';
    file.textContent = s.file ? ('文件：' + s.file) : '文件：—（现在没在打）';
    pct.textContent = s.pct + '%';
    pb.style.width = s.pct + '%';
    left.textContent = s.left;
    eta.textContent = s.eta;
    layer.textContent = s.layer;
    nz.textContent = s.nozzle;
    bd.textContent = s.bed;
    ch.textContent = s.chamber;
    cool.textContent = s.cool || '';
    misc.textContent = s.misc || '';
    if (s.cam_n >= 0) cmisc.textContent = '摄像头已收 ' + s.cam_n + ' 帧，最近一帧 ' + s.cam_age + ' 秒前';
    else cmisc.textContent = '摄像头没开（电脑上看板里点「开摄像头」）';
    lmapinfo.textContent = s.layer_info || (s.layers_ready ? '等打印机报层号…' : '层图还没准备好（这盘的 3mf 要在打印机 /cache 里）');
    posinfo.textContent = s.marker_px
      ? ('喷头估算：像素 ' + s.marker_px + ' → 盘上 ' + (s.marker_mm || '算不出来（标定不完整）') + ' mm'
         + '　｜　标定点 X ' + (s.cal_x && s.cal_x.length
              ? s.cal_x.map(function(v){ return v === null ? '—' : Math.round(v); }).join(' / ') : '空')
         + '　Y ' + (s.cal_y && s.cal_y.length
              ? s.cal_y.map(function(v){ return v === null ? '—' : Math.round(v); }).join(' / ') : '空')
         + '　｜　盘子前沿 y=' + s.plate_edge_y)
      : '喷头估算：还没抓到标记（电脑上看板切到「摄像头·蓝标」）';
    if (s.toast && s.toast.id && s.toast.id !== lastToastId) {
      lastToastId = s.toast.id;
      showToast(s.toast);
    }
    fillStatus(s);
    fillGauges(s);
    if (s.layer_n && s.layer_n !== lastLayerN) {
      lastLayerN = s.layer_n;
      lmap.src = '/api/layer.png?n=' + s.layer_n + '&t=' + Date.now();
    }
  }catch(e){ state.textContent = '连不上电脑上的看板'; }
}
function light(on){ fetch('/api/light?on=' + on); }
var lastToastId = 0, toastTimer = null;
function showLogin(){
  const box = document.getElementById('login');
  box.style.display = 'block';
  try{ document.getElementById('logincode').focus(); }catch(e){}
}
async function doLogin(){
  const el = document.getElementById('logincode');
  const msg = document.getElementById('loginmsg');
  const c = (el.value || '').trim();
  if (!c){ msg.textContent = '先输访问码'; return; }
  try{
    const d = await (await fetch('/api/login?code=' + encodeURIComponent(c), {cache:'no-store'})).json();
    if (d.ok){ location.reload(); }
    else { msg.textContent = d.msg || '访问码不对'; }
  }catch(e){ msg.textContent = '连不上电脑上的看板'; }
}
function esc(v){ return String(v === null || v === undefined ? '' : v).replace(/[&<>]/g, function(c){ return c === '&' ? '&amp;' : (c === '<' ? '&lt;' : '&gt;'); }); }
function dot(k){ return '<span style="display:inline-block;width:9px;height:9px;border-radius:50%;margin-right:7px;flex:0 0 auto;margin-top:7px;background:' + (k === 'ok' ? '#3fb950' : (k === 'warn' ? '#e0a33e' : '#ff6b6b')) + '"></span>'; }
function pair(v){ return (v && v.length) ? v.map(function(e){ return e === null ? '—' : Math.round(e); }).join(' / ') : '空'; }
function dial(label, val, max, tgt, unit, hue){
  const cx = 60, cy = 60, r = 44;
  const known = (val !== null && val !== undefined);
  const frac = known ? Math.max(0, Math.min(1, val / max)) : 0;
  const rad = (180 + 180 * frac) * Math.PI / 180;
  const nx = cx + (r - 9) * Math.cos(rad), ny = cy + (r - 9) * Math.sin(rad);
  const len = Math.PI * r;
  let tick = '';
  if (tgt !== null && tgt !== undefined && max > 0 && tgt > 0){
    const ta = (180 + 180 * Math.max(0, Math.min(1, tgt / max))) * Math.PI / 180;
    tick = '<line x1="' + (cx + (r - 13) * Math.cos(ta)) + '" y1="' + (cy + (r - 13) * Math.sin(ta))
         + '" x2="' + (cx + (r + 3) * Math.cos(ta)) + '" y2="' + (cy + (r + 3) * Math.sin(ta))
         + '" stroke="#ffd166" stroke-width="3"/>';
  }
  let svg = '<svg width="118" height="84" viewBox="0 0 120 84">';
  svg += '<path d="M ' + (cx - r) + ' ' + cy + ' A ' + r + ' ' + r + ' 0 0 1 ' + (cx + r) + ' ' + cy
       + '" fill="none" stroke="#2a3038" stroke-width="9"/>';
  if (known){
    svg += '<path d="M ' + (cx - r) + ' ' + cy + ' A ' + r + ' ' + r + ' 0 0 1 ' + (cx + r) + ' ' + cy
         + '" fill="none" stroke="' + hue + '" stroke-width="9" stroke-dasharray="' + (len * frac) + ' ' + len + '"/>';
  }
  svg += tick;
  svg += '<line x1="' + cx + '" y1="' + cy + '" x2="' + nx + '" y2="' + ny + '" stroke="#e6edf3" stroke-width="3" stroke-linecap="round"/>';
  svg += '<circle cx="' + cx + '" cy="' + cy + '" r="5" fill="#e6edf3"/>';
  svg += '<text x="' + cx + '" y="' + (cy - 12) + '" text-anchor="middle" fill="#e6edf3" font-size="16" font-weight="700">'
       + (known ? Math.round(val * 10) / 10 : '—') + '</text>';
  svg += '<text x="' + cx + '" y="' + (cy + 15) + '" text-anchor="middle" fill="#8b93a0" font-size="11">' + unit + '</text>';
  svg += '</svg>';
  return '<div style="text-align:center;min-width:118px">' + svg
       + '<div style="font-size:12px;color:#8b93a0;margin-top:-6px">' + esc(label)
       + ((tgt !== null && tgt !== undefined && tgt > 0) ? ('（目标 ' + tgt + '）') : '') + '</div></div>';
}
function fillGauges(s){
  const g = [
    dial('喷嘴', s.nozzle_now, 300, s.nozzle_tgt, '°C', '#ff7b72'),
    dial('热床', s.bed_now, 100, s.bed_tgt, '°C', '#ffa657'),
    dial('腔温', s.chamber_num, 60, null, '°C', '#79c0ff'),
    dial('模型风扇', s.fan_model, 100, null, '%', '#56d364'),
    dial('辅助风扇', s.fan_aux, 100, null, '%', '#3fb950'),
    dial('热端风扇', s.fan_hotend, 100, null, '%', '#7ee787')
  ];
  document.getElementById('gauges').innerHTML = g.join('');
}
function fillStatus(s){
  const camOn = s.cam_n >= 0;
  const rows = [
    ['电脑看板服务', '在线 —— 这个页面就是它给的', 'ok'],
    ['打印机连接 MQTT', s.conn ? '已连接' : '断开 / 正在重连', s.conn ? 'ok' : 'bad'],
    ['摄像头', camOn ? ('在线，已收 ' + s.cam_n + ' 帧，最近一帧 ' + s.cam_age + ' 秒前') : '没开，或者断了', camOn ? 'ok' : 'bad'],
    ['打印状态', s.state || '—', (s.state === '运行中' || s.state === '已完成') ? 'ok' : 'warn'],
    ['当前文件', s.file || '—（现在没在打）', s.file ? 'ok' : 'warn'],
    ['任务名', s.task || '—', 'ok'],
    ['阶段', s.stage || '—', 'ok'],
    ['进度', (s.pct === null || s.pct === undefined) ? '—' : (s.pct + '%'), 'ok'],
    ['剩余时间', s.left || '—', 'ok'],
    ['预计完成', s.eta || '—', 'ok'],
    ['层号', s.layer || '—', 'ok'],
    ['喷嘴温度（当前 / 目标）', s.nozzle || '—', 'ok'],
    ['热床温度（当前 / 目标）', s.bed || '—', 'ok'],
    ['腔温', s.chamber || '—', 'ok'],
    ['降温估计', s.cool || '—', 'ok'],
    ['风扇 / WiFi / 耗材', s.misc || '—', 'ok'],
    ['层图', s.layer_info || (s.layers_ready ? '等打印机报层号…' : '还没准备好（3mf 要在打印机 /cache 里）'), s.layers_ready ? 'ok' : 'warn'],
    ['标记来源', s.marker_src || '—', 'ok'],
    ['喷头位置估算', s.marker_px ? (s.marker_px + ' → 盘上 ' + (s.marker_mm || '算不出来') + ' mm') : '还没抓到标记', s.marker_px ? 'warn' : 'bad'],
    ['标定点 X（左 / 右）', pair(s.cal_x), (s.cal_x && s.cal_x.length === 2) ? 'ok' : 'warn'],
    ['标定点 Y（前 / 后）', pair(s.cal_y), (s.cal_y && s.cal_y.length === 2) ? 'ok' : 'warn'],
    ['盘子前沿像素 y', (s.plate_edge_y === null || s.plate_edge_y === undefined) ? '—' : s.plate_edge_y, s.plate_edge_y ? 'ok' : 'bad'],
    ['最近一条提示', (s.toast && s.toast.title) ? (s.toast.title + '　' + (s.toast.text || '')) : '（还没有）', 'ok']
  ];
  let h = '';
  for (let i = 0; i < rows.length; i++){
    h += '<div style="display:flex;align-items:flex-start">' + dot(rows[i][2])
       + '<span style="opacity:.7;min-width:140px">' + esc(rows[i][0]) + '</span>'
       + '<span style="flex:1">' + esc(rows[i][1]) + '</span></div>';
  }
  document.getElementById('statuslist').innerHTML = h;
}
function showToast(t){
  const box = document.getElementById('toast');
  document.getElementById('toast_t').textContent = t.title || '提示';
  document.getElementById('toast_x').textContent = t.text || '';
  box.style.borderColor = t.kind === 'bad' ? '#ff6b6b' : (t.kind === 'warn' ? '#e0a33e' : '#4ea1ff');
  box.style.display = 'block';
  if (toastTimer) clearTimeout(toastTimer);
  toastTimer = setTimeout(function(){ box.style.display = 'none'; }, 9000);
}
async function cal(c){
  const el = document.getElementById('calinfo');
  try{
    const d = await (await fetch('/api/cal?corner=' + c, {cache:'no-store'})).json();
    el.textContent = d.msg || (d.ok ? '记下了' : '没成功');
    if (d.ok) tick();
  }catch(e){ el.textContent = '调用失败：连不上电脑上的看板'; }
}
async function cam(){
  const el = document.getElementById('cam');
  const url = '/api/cam.jpg?t=' + Date.now();
  // 用 probe 先试有没有帧：微信内置浏览器对 fetch+blob 不一定认，直接塞地址最稳
  const probe = new Image();
  probe.onload = function(){
    el.src = url;
    el.style.display = 'block';
    camn.textContent = '约 0.5 帧/秒（A1 摄像头就这速度）';
  };
  probe.onerror = function(){
    camn.textContent = '电脑那边还没出画面（摄像头没开，或者刚断开正在重连）';
  };
  probe.src = url;
}
function camAnnot(){
  const el = document.getElementById('camannot');
  el.src = '/api/cam_annot.jpg?t=' + Date.now();
}
setInterval(camAnnot, 3000); camAnnot();
let tab = '';
let lastLayerN = -1;
function show(t){
  tab = t;
  ['hist','events','ctrl','raw'].forEach(function(k){
    var el = document.getElementById('p_' + k);
    if (el) el.style.display = (k === t) ? 'block' : 'none';
  });
  document.querySelectorAll('.tabbtn').forEach(function(b){
    b.classList.toggle('on', b.dataset.t === t);
  });
  if (t === 'hist') loadHist(0);
  if (t === 'events') loadEvents();
  if (t === 'raw') loadRaw();
  if (t === 'ctrl') loadReply();
}
async function loadEvents(){
  try{ const d = await (await fetch('/api/events',{cache:'no-store'})).json();
       events.textContent = d.lines.slice(-300).join('\n'); }catch(e){}
}
async function loadRaw(){
  try{ const d = await (await fetch('/api/raw',{cache:'no-store'})).json();
       raw.textContent = d.lines.join('\n'); }catch(e){}
}
async function loadReply(){
  try{ const d = await (await fetch('/api/reply',{cache:'no-store'})).json();
       reply.textContent = d.lines.length ? d.lines.slice(-40).join('\n') : '(还没有指令)'; }catch(e){}
}
let histLoaded = false;
async function loadHist(force){
  if (histLoaded && !force) return;
  try{
    const d = await (await fetch('/api/history' + (force ? '?r=1' : ''), {cache:'no-store'})).json();
    if (!d.files.length){ hist.textContent = '还没有读到（点「重新读取」，或者电脑那边没连打印机）'; return; }
    histLoaded = true;
    hist.innerHTML = '';
    d.files.slice().reverse().forEach(function(f){
      const row = document.createElement('div');
      row.style.margin = '6px 0';
      const a = document.createElement('span');
      a.textContent = f.when + '   ' + f.size + '   ';
      const b1 = document.createElement('span');
      b1.textContent = '看封面';
      b1.style.cssText = 'color:#3ea6ff;margin-right:10px';
      b1.onclick = function(){ loadThumb(f.name); };
      const b2 = document.createElement('span');
      b2.textContent = '下载';
      b2.style.cssText = 'color:#4ad07a';
      b2.onclick = function(){ location.href = '/api/file?dir=/timelapse&name=' + encodeURIComponent(f.name); };
      row.appendChild(a); row.appendChild(b1); row.appendChild(b2);
      hist.appendChild(row);
    });
  }catch(e){ hist.textContent = '读不到'; }
}
function loadThumb(name){
  const el = document.getElementById('hthumb');
  el.style.display = 'block';
  el.src = '/api/thumb?name=' + encodeURIComponent(name.replace(/\.avi$/i, '.jpg'));
}
function cmd(q){
  fetch('/api/cmd?' + q).then(function(){ setTimeout(loadReply, 800); });
}
function drawChart(s){
  const c = document.getElementById('chart');
  let w = c.clientWidth;
  if (!w) { w = (c.parentNode && c.parentNode.clientWidth) || 320; }  // 有些浏览器第一帧量到 0
  const h = 170, pad = 26;
  c.width = w * 2; c.height = h * 2;
  const g = c.getContext('2d'); g.scale(2, 2);
  g.clearRect(0, 0, w, h);
  g.strokeStyle = '#39434f'; g.lineWidth = 1;
  g.beginPath(); g.moveTo(pad, h - pad); g.lineTo(w - 4, h - pad);
  g.moveTo(pad, 4); g.lineTo(pad, h - pad); g.stroke();
  if (!s || s.length < 2){ g.fillStyle = '#8b98a8'; g.fillText('在采数据…', pad + 8, 18); return; }
  let top = 60;
  s.forEach(function(p){ top = Math.max(top, p[0], p[1], p[2], p[3]); });
  top = Math.ceil((top + 10) / 10) * 10;
  g.fillStyle = '#8b98a8'; g.font = '10px monospace';
  g.fillText(top + '°C', 2, 12); g.fillText('0°C', 2, h - pad - 4);
  const step = (w - pad - 8) / (s.length - 1);
  function line(i, col, width, dash){
    g.strokeStyle = col; g.lineWidth = width; g.setLineDash(dash || []);
    g.beginPath();
    s.forEach(function(p, k){
      const x = pad + k * step, y = (h - pad) - (p[i] / top) * (h - pad - 8);
      if (k === 0) g.moveTo(x, y); else g.lineTo(x, y);
    });
    g.stroke(); g.setLineDash([]);
  }
  line(2, '#a3502f', 1, [5, 4]);
  line(3, '#2e7f76', 1, [5, 4]);
  line(0, '#ff6b4a', 2);
  line(1, '#4ad6c0', 2);
}
setInterval(tick,2000); tick();
setInterval(cam,3000); cam();
setInterval(chartTick,3000);
// 转屏 / 改窗口大小之后重画（不然画布会按旧宽度拉伸）
window.addEventListener('resize', chartTick);
window.addEventListener('orientationchange', function(){ setTimeout(chartTick, 400); });
async function chartTick(){
  try{ const d = await (await fetch('/api/chart',{cache:'no-store'})).json(); drawChart(d.samples); }catch(e){}
}
// 只在网址后面加 ?dbg=1 时才出现 —— 用来量是谁把页面撑宽了
if (location.search.indexOf('dbg') >= 0) {
  const d = document.createElement('div');
  d.style.cssText = 'position:fixed;left:0;bottom:0;right:0;background:#000;color:#ff0;' +
                    'font:11px monospace;padding:6px;z-index:99;white-space:pre-wrap';
  document.body.appendChild(d);
  function dbg(){
    let bad = [];
    document.querySelectorAll('*').forEach(function(el){
      const r = el.getBoundingClientRect();
      if (r.width > 0 && r.right > window.innerWidth + 1) {
        bad.push((el.id ? '#' + el.id : (el.className ? '.' + el.className : el.tagName)) +
                 '=' + Math.round(r.right));
      }
    });
    d.textContent = 'innerWidth=' + window.innerWidth +
      '  scrollWidth=' + document.documentElement.scrollWidth +
      '  bodyScroll=' + document.body.scrollWidth +
      '\n超出的元素: ' + (bad.slice(0, 8).join('  ') || '没有');
  }
  setInterval(dbg, 600); dbg();
}
chartTick();
</script></body></html>
"""


def log(msg):
    line = "%s  %s\n" % (datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"), msg)
    try:
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(line)
    except OSError:
        pass


def log_exc(where):
    log("!! %s 出错:\n%s" % (where, traceback.format_exc()))


def read_studio_conf():
    try:
        with open(STUDIO_CONF, "r", encoding="utf-8") as f:
            text = f.read()
    except OSError:
        return None, None
    m = re.search(r'"access_code"\s*:\s*\{\s*"([^"]+)"\s*:\s*"([^"]+)"', text)
    return (m.group(1), m.group(2)) if m else (None, None)


def local_subnet():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("223.5.5.5", 80))
        return s.getsockname()[0]
    except OSError:
        return None
    finally:
        s.close()


def scan_for_printer(timeout=0.25, logf=None):
    me = local_subnet()
    if not me:
        return []
    head = me.rsplit(".", 1)[0]
    found = []

    def probe(i):
        c = socket.socket()
        c.settimeout(timeout)
        try:
            if c.connect_ex(("%s.%d" % (head, i), 8883)) == 0:
                found.append("%s.%d" % (head, i))
        except OSError:
            pass
        finally:
            c.close()

    batch = []
    for i in range(1, 255):
        t = threading.Thread(target=probe, args=(i,), daemon=True)
        t.start()
        batch.append(t)
        if len(batch) >= 64:
            for t2 in batch:
                t2.join()
            batch = []
    for t in batch:
        t.join()
    if logf:
        logf("扫描完成, 发现: %s" % sorted(found))
    return sorted(found)


def load_cfg():
    try:
        with open(CONF_JSON, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_cfg(cfg):
    try:
        with open(CONF_JSON, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except OSError:
        log_exc("save_cfg")


def fmt_left(minutes):
    try:
        m = int(minutes)
    except (TypeError, ValueError):
        return "—"
    if m <= 0:
        return "—"
    h, mm = divmod(m, 60)
    return ("%d 小时 %02d 分" % (h, mm)) if h else ("%d 分" % mm)


def eta_text(minutes):
    try:
        m = int(minutes)
    except (TypeError, ValueError):
        return "—"
    return (datetime.datetime.now() + datetime.timedelta(minutes=m)).strftime("%H:%M") if m > 0 else "—"


def fmt_min(seconds):
    """秒 -> 「X 分」/「X 小时 Y 分」"""
    try:
        s = float(seconds)
    except (TypeError, ValueError):
        return "?"
    if s <= 0:
        return "0 分"
    m = s / 60.0
    if m < 1:
        return "不到 1 分"
    if m < 90:
        return "%.0f 分" % m
    return "%.1f 小时" % (m / 60.0)


def fmt_size(n):
    try:
        n = float(n)
    except (TypeError, ValueError):
        return "?"
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return ("%.0f %s" % (n, unit)) if unit == "B" else ("%.1f %s" % (n, unit))
        n /= 1024.0
    return "?"


def color_of(hexstr):
    h = (hexstr or "FFFFFFFF").strip()
    return "#" + h[:6].lower() if len(h) >= 6 else "#888888"


def decode_net(info):
    """打印机的 net 字段把 IP 打包成整数了, 解出来。"""
    try:
        ip = struct.pack(">I", int(info["ip"]))
        return ".".join(str(b) for b in ip)
    except Exception:
        return "?"


# --------------------------------------------------------------------------- #
#  层图：从 gcode 里算出"这一层在盘上打哪儿"
# --------------------------------------------------------------------------- #
GRID = 128                      # 盘 256mm 分成 128 格 -> 一格 2mm
CELL_MM = 256.0 / GRID
LAYER_PX = 560                  # 层图画多大（像素）
CAM_FULL_W, CAM_FULL_H = 1536, 1080   # A1 摄像头原始分辨率
CAL_W, CAL_H = 960, 675         # 标定窗口里的显示尺寸（原图的 0.625 倍）
RECOG_DIR = r"D:\deeseek工作区喵\_tools\cam_test"   # 识别图存这儿（自动存，只留最近 30 张）
RECOG_KEEP = 30
RECOG_EVERY = 30.0              # 秒，自动存的间隔
MOVE_RE = re.compile(r"^G1\s+.*\bX(-?[0-9.]+)\s+Y(-?[0-9.]+).*\bE-?[0-9.]")


def find_color_blobs(jpeg_bytes, kind="blue", min_cells=10, min_fill=0.15):
    """在画面里找出所有"像标记"的块。返回 [{n, x, y}]（坐标是全分辨率像素）。

    kind = "blue"（原来那张二维码防伪标，蓝点是稀疏的）
         = "red" （老大后来加的纯色红标，好认得多）
    ⚠️ min_fill 要放宽：二维码的蓝点稀疏，实心度只有 0.2 左右；
       用 0.35 会把标签整个筛掉（踩过）。
    挑哪个由调用方决定 —— 画面里可能有别的同色东西（背景、青色打印件）。
    """
    if not jpeg_bytes or Image is None:
        return []
    try:
        im = Image.open(io.BytesIO(jpeg_bytes)).convert("RGB")
    except Exception:
        return []
    s = 4
    small = im.resize((im.width // s, im.height // s), Image.NEAREST)
    px = small.load()
    w, h = small.size
    m = bytearray(w * h)
    for y in range(h):
        row = y * w
        for x in range(w):
            r, g, b = px[x, y]
            if kind == "red":
                if r > 110 and r > g + 45 and r > b + 45:
                    m[row + x] = 1
            else:
                if b > 100 and b > r + 40 and b > g + 25:
                    m[row + x] = 1
    seen = bytearray(w * h)
    out = []
    for i in range(w * h):
        if not m[i] or seen[i]:
            continue
        q = deque([i])
        seen[i] = 1
        cells = []
        while q:
            c = q.popleft()
            cells.append(c)
            cy, cx = divmod(c, w)
            for ny, nx in ((cy - 1, cx), (cy + 1, cx), (cy, cx - 1), (cy, cx + 1)):
                if 0 <= ny < h and 0 <= nx < w:
                    j = ny * w + nx
                    if m[j] and not seen[j]:
                        seen[j] = 1
                        q.append(j)
        if len(cells) < min_cells:
            continue
        xs = [c % w for c in cells]
        ys = [c // w for c in cells]
        area = (max(xs) - min(xs) + 1) * (max(ys) - min(ys) + 1) or 1
        if len(cells) / float(area) < min_fill:
            continue
        out.append({"n": len(cells),
                    "x": sum(xs) / float(len(xs)) * s,
                    "y": sum(ys) / float(len(ys)) * s})
    out.sort(key=lambda d: -d["n"])
    return out


def find_blue_blobs(jpeg_bytes, min_cells=10, min_fill=0.15):
    """兼容旧调用：只找蓝的。"""
    return find_color_blobs(jpeg_bytes, "blue", min_cells, min_fill)


def find_marker_blobs(jpeg_bytes):
    """找标记：红的优先（老大贴的纯色红标），没有红块再找蓝的。"""
    red = find_color_blobs(jpeg_bytes, "red")
    return red if red else find_color_blobs(jpeg_bytes, "blue")


def num(v):
    """把可能是字符串的数字转成 float，转不了就 None（给网页画仪表用）。"""
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


def annotate_jpeg(jpeg_bytes, marker_px=None, edge_y=None, blobs=None, note="",
                  quality=78):
    """在画面上把识别结果画出来，返回 JPEG 字节。

    红线 = 盘子前沿（用来推前后位置）；青框 = 所有候选标记；黄框 = 锁定的标记；
    底下黑条 = 识别结果文字。
    """
    if not jpeg_bytes or Image is None:
        return None
    try:
        im = Image.open(io.BytesIO(jpeg_bytes)).convert("RGB")
    except Exception:
        return None
    d = ImageDraw.Draw(im)
    # 坐标网格 + 刻度：每 100 像素一条淡线，边上写数字（图里所有位置都能对着读）
    for gx in range(0, im.width, 100):
        d.line((gx, 0, gx, im.height), fill=(72, 76, 84), width=1)
        d.text((gx + 3, 4), str(gx), fill=(152, 158, 166))
    for gy in range(0, im.height, 100):
        d.line((0, gy, im.width, gy), fill=(72, 76, 84), width=1)
        d.text((4, gy + 3), str(gy), fill=(152, 158, 166))
    if edge_y:
        d.line((0, edge_y, im.width, edge_y), fill=(255, 60, 60), width=5)
        d.text((8, edge_y + 6), "plate front edge y=%d" % edge_y, fill=(255, 60, 60))
    for b in (blobs or [])[:4]:
        d.rectangle((b["x"] - 26, b["y"] - 26, b["x"] + 26, b["y"] + 26),
                    outline=(60, 220, 255), width=4)
    if marker_px:
        x, y = marker_px
        d.rectangle((x - 30, y - 30, x + 30, y + 30), outline=(255, 255, 0), width=4)
        d.line((x - 46, y, x + 46, y), fill=(255, 255, 0), width=3)
        d.line((x, y - 46, x, y + 46), fill=(255, 255, 0), width=3)
    if note:
        d.rectangle((0, im.height - 32, im.width, im.height), fill=(0, 0, 0))
        d.text((8, im.height - 24), note[:110], fill=(255, 255, 0))
    buf = io.BytesIO()
    try:
        im.save(buf, "JPEG", quality=quality)
    except Exception:
        return None
    return buf.getvalue()


def plate_front_edge_y(jpeg_bytes, bx0=0.42, bx1=0.62, y0=150, y1=760):
    """找**盘子前沿**在画面里的 y 像素（深色盘面 -> 亮色床架 的分界线）。

    为什么需要它：A1 是床动式，前后轴动的是**底盘**，喷头本身前后不动。
    所以「前后位置」只能靠看盘子在画面里的位置来推 —— 盘子前沿跟着底盘走。

    做法：在画面中间取一条竖直带，按行算平均亮度，
    从上往下找**亮度增加最多**的那一行（dark 盘面 -> bright 床架）。
    返回 y 像素；找不到返回 None。
    """
    if not jpeg_bytes or Image is None:
        return None
    try:
        im = Image.open(io.BytesIO(jpeg_bytes)).convert("L")
    except Exception:
        return None
    w, h = im.size
    x0 = int(w * bx0)
    x1 = int(w * bx1)
    px = im.load()
    prof = []
    for y in range(y0, min(y1, h)):
        s = 0
        for x in range(x0, x1):
            s += px[x, y]
        prof.append(s / float(x1 - x0))
    if len(prof) < 12:
        return None
    # 平滑一下再找最大正梯度
    sm = [sum(prof[max(0, i - 1):i + 2]) / len(prof[max(0, i - 1):i + 2])
          for i in range(len(prof))]
    best_i, best_g = None, 0.0
    for i in range(3, len(sm) - 3):
        g = sm[i + 2] - sm[i - 2]
        if g > best_g:
            best_g, best_i = g, i
    if best_i is None or best_g < 6.0:      # 6 灰阶以下认为没找到明显边
        return None
    return y0 + best_i


def pick_blue_blob(blobs, target=None, max_jump=700.0):
    """挑一个块：锁定过就取离上次最近的，没锁定就取最大的。"""
    if not blobs:
        return None
    if target:
        best = min(blobs, key=lambda b: math.hypot(b["x"] - target[0], b["y"] - target[1]))
        if math.hypot(best["x"] - target[0], best["y"] - target[1]) <= max_jump:
            return best
    return blobs[0]


def detect_blue_marker(jpeg_bytes):
    """图省事的版本：直接返回最大的那块的中心。"""
    b = pick_blue_blob(find_blue_blobs(jpeg_bytes))
    return (b["x"], b["y"]) if b else None


def solve3(A, b):
    """解 3x3 线性方程组（克拉默法则）。奇异返回 None。"""
    def det3(m):
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
                - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))
    D = det3(A)
    if abs(D) < 1e-9:
        return None
    out = []
    for col in range(3):
        M = [row[:] for row in A]
        for r in range(3):
            M[r][col] = b[r]
        out.append(det3(M) / D)
    return out


def fit_affine(pairs):
    """3 组 ((px,py),(x,y)) -> 仿射的 6 个参数 (a,b,c,d,e,f)。

    X = a*px + b*py + c
    Y = d*px + e*py + f
    返回 (params, residual_mm)；点不够或奇异返回 (None, None)。
    """
    if len(pairs) < 3:
        return None, None
    p = pairs[:3]
    A = [[px, py, 1.0] for (px, py), _ in p]
    bx = [mm[0] for _, mm in p]
    by = [mm[1] for _, mm in p]
    sx = solve3(A, bx)
    sy = solve3(A, by)
    if not sx or not sy:
        return None, None
    params = (sx[0], sx[1], sx[2], sy[0], sy[1], sy[2])
    # 残差：拿全部点算一遍（只 3 点时必然为 0）
    err = 0.0
    for (px, py), (mx, my) in pairs:
        ex = params[0] * px + params[1] * py + params[2] - mx
        ey = params[3] * px + params[4] * py + params[5] - my
        err = max(err, math.hypot(ex, ey))
    return params, err


def apply_affine(params, px, py):
    return (params[0] * px + params[1] * py + params[2],
            params[3] * px + params[4] * py + params[5])


def homography_from_quad(quad):
    """盘子单位坐标 (u,v ∈ 0..1) -> 图像像素 的单应矩阵（Heckbert 闭式解）。

    quad 按 (u,v) = (0,0) (1,0) (1,1) (0,1) 的顺序给，也就是
    左前 -> 右前 -> 右后 -> 左后。
    """
    (x0, y0), (x1, y1), (x2, y2), (x3, y3) = quad
    dx1 = x1 - x2
    dx2 = x3 - x2
    dx3 = x0 - x1 + x2 - x3
    dy1 = y1 - y2
    dy2 = y3 - y2
    dy3 = y0 - y1 + y2 - y3
    if abs(dx3) < 1e-9 and abs(dy3) < 1e-9:
        g = h = 0.0
    else:
        den = dx1 * dy2 - dx2 * dy1
        if abs(den) < 1e-12:
            return None
        g = (dx3 * dy2 - dx2 * dy3) / den
        h = (dx1 * dy3 - dx3 * dy1) / den
    return [[x1 - x0 + g * x1, x3 - x0 + h * x3, x0],
            [y1 - y0 + g * y1, y3 - y0 + h * y3, y0],
            [g, h, 1.0]]


def invert3(m):
    a, b, c = m[0]
    d, e, f = m[1]
    g, h, i = m[2]
    A = e * i - f * h
    B = -(d * i - f * g)
    C = d * h - e * g
    det = a * A + b * B + c * C
    if abs(det) < 1e-12:
        return None
    return [[A / det, -(b * i - c * h) / det, (b * f - c * e) / det],
            [B / det, (a * i - c * g) / det, -(a * f - c * d) / det],
            [C / det, -(a * h - b * g) / det, (a * e - b * d) / det]]


def apply_homography(m, u, v):
    w = m[2][0] * u + m[2][1] * v + m[2][2]
    if abs(w) < 1e-12:
        return None
    return ((m[0][0] * u + m[0][1] * v + m[0][2]) / w,
            (m[1][0] * u + m[1][1] * v + m[1][2]) / w)


def parse_layers(text):
    """把 gcode 切成一层一块的位图。

    返回 (layers, bboxes, lh, initial)：
      layers[i] = bytearray(GRID*GRID)，1 = 这一层这里要挤出
      bboxes[i] = (minx, miny, maxx, maxy) 毫米
      lh / initial = 层高 / 首层高（从头部注释里读）
    只认带 E 的移动（真挤出），空走不要。
    """
    layers = []
    bboxes = []
    cur = None
    prev = None
    bb = None
    lh = 0.2
    initial = 0.2
    for ln in text.splitlines():
        if cur is None and ln.startswith(";"):
            m = re.match(r";\s*layer_height\s*=\s*([0-9.]+)", ln)
            if m:
                lh = float(m.group(1))
            m = re.match(r";\s*initial_layer_print_height\s*=\s*([0-9.]+)", ln)
            if m:
                initial = float(m.group(1))
        if ln.startswith("; CHANGE_LAYER"):
            cur = bytearray(GRID * GRID)
            layers.append(cur)
            bboxes.append(None)
            bb = None
            prev = None
            continue
        if cur is None:
            continue
        m = MOVE_RE.match(ln)
        if not m:
            continue
        x = float(m.group(1))
        y = float(m.group(2))
        if bb is None:
            bb = [x, y, x, y]
        else:
            bb[0] = min(bb[0], x)
            bb[1] = min(bb[1], y)
            bb[2] = max(bb[2], x)
            bb[3] = max(bb[3], y)
        bboxes[-1] = tuple(bb)
        if prev is not None:
            x0, y0 = prev
            steps = int(max(abs(x - x0), abs(y - y0)) / 1.2) + 1
            for i in range(1, steps + 1):
                xi = x0 + (x - x0) * i / steps
                yi = y0 + (y - y0) * i / steps
                cx = int(xi / CELL_MM)
                cy = int(yi / CELL_MM)
                if 0 <= cx < GRID and 0 <= cy < GRID:
                    cur[cy * GRID + cx] = 1
        prev = (x, y)
    return layers, bboxes, lh, initial


def make_qr(text, box=9, border=3):
    """生成二维码图片（微信扫的就是这个）。没装 qrcode 就返回 None。"""
    try:
        import qrcode
    except ImportError:
        return None
    q = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M,
                      box_size=box, border=border)
    q.add_data(text)
    q.make(fit=True)
    return q.make_image(fill_color="black", back_color="white").convert("RGB")


# --------------------------------------------------------------------------- #
#  降温模型
# --------------------------------------------------------------------------- #
class CoolModel:
    """从看板自己的温度采样里拟合真实的降温时间常数。

    用牛顿冷却定律: T(t) = T环境 + (T0 - T环境) * e^(-t/τ)
    两边取对数: ln(T - T环境) = ln(T0 - T环境) - t/τ   ->  对 t 做直线拟合, 斜率就是 -1/τ。
    只有真的在降温（目标降到 45 度以下、温度还高、而且在往下走）才采数据。

    没测到之前用 TAU_DEFAULT 里的粗估常数, 界面上会写清楚是「粗估」还是「实测」。
    """

    def __init__(self):
        self.buf = {"nozzle": [], "bed": []}
        self.tau = {}

    def add(self, t, nozzle, bed, nz_t, bd_t):
        for key, temp, tgt in (("nozzle", nozzle, nz_t), ("bed", bed, bd_t)):
            try:
                temp = float(temp)
                tgt = float(tgt)
            except (TypeError, ValueError):
                continue
            if tgt <= 45.0 and temp > COOL_ENV + 12.0:
                buf = self.buf[key]
                if buf and temp > buf[-1][1] + 0.5:
                    buf.clear()          # 又升上去了, 这一段作废
                buf.append((t, temp))
                if len(buf) > 900:
                    del buf[0]
            else:
                if len(self.buf[key]) >= 15:
                    self._fit(key)
                self.buf[key] = []

    def _fit(self, key):
        pts = self.buf[key]
        xs = [p[0] - pts[0][0] for p in pts]
        ys = [math.log(max(1.0, p[1] - COOL_ENV)) for p in pts]
        n = len(xs)
        mx = sum(xs) / n
        my = sum(ys) / n
        num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        den = sum((x - mx) ** 2 for x in xs)
        if den <= 0:
            return
        slope = num / den
        if slope < -1e-5:
            tau = min(7200.0, max(20.0, -1.0 / slope))
            self.tau[key] = tau
            log("拟合出 %s 的降温时间常数 τ=%.0f 秒 (用了 %d 个采样点)" % (key, tau, n))

    def get_tau(self, key):
        return self.tau.get(key, TAU_DEFAULT[key])

    def source(self, key):
        return ("实测 %.1f 分" % (self.tau[key] / 60.0)) if key in self.tau else "粗估"


def cool_estimate(tau, temp, goal, env=COOL_ENV):
    """还要多久凉到 goal 度。返回秒。"""
    if temp <= goal:
        return 0.0
    if goal <= env or temp <= env:
        return None
    return tau * math.log((temp - env) / (goal - env))


# --------------------------------------------------------------------------- #
#  MQTT
# --------------------------------------------------------------------------- #
class PrinterLink:
    def __init__(self, host, serial, code, q):
        self.host = host
        self.serial = serial
        self.code = code
        self.q = q
        self.state = {}
        self.version = {}
        self.lock = threading.Lock()
        self.client = None
        self.seq = 0
        self.connected = False
        self.full_seen = False

    def _next_seq(self):
        self.seq += 1
        return str(self.seq)

    def send(self, obj, note="", qos=0):
        """发命令。

        ⚠️ 实测教训: 全部用 QoS 0。
        文档说 print.pause/stop/resume 要用 QoS 1, 我改成 QoS 1 之后,
        这台 A1 的局域网 broker 直接把会话断了 —— 结果连原本能用的灯光也不响应了。
        所以统一 QoS 0。
        """
        if not self.client:
            return False
        try:
            self.client.publish("device/%s/request" % self.serial, json.dumps(obj), qos=qos)
            if note:
                self.q.put(("event", "发出指令: " + note))
                self.q.put(("cmd_sent", note))
            return True
        except Exception:
            log_exc("publish")
            return False

    def _on_connect(self, c, u, flags, rc, properties=None):
        txt = str(rc)
        if "success" not in txt.lower() and txt != "0":
            # 被拒了 —— 最常见的原因是打印机换了访问码（切局域网模式会换）
            self.connected = False
            log("MQTT 被拒 rc=%s" % txt)
            self.q.put(("conn", "被拒: " + txt))
            self.q.put(("auth_bad", txt))
            return
        self.connected = True
        log("MQTT 连上了 %s (%s) rc=%s" % (self.host, self.serial, rc))
        c.subscribe("device/%s/report" % self.serial)
        self.send({"pushing": {"sequence_id": self._next_seq(), "command": "pushall",
                               "version": 1, "push_target": 1}})
        self.send({"info": {"sequence_id": self._next_seq(), "command": "get_version"}})
        self.q.put(("conn", "连上了"))

    def _on_disconnect(self, c, u, *args):
        self.connected = False
        log("MQTT 断开了")
        self.q.put(("conn", "断线, 正在重连…"))
        self.q.put(("event", "MQTT 断线了"))

    def _on_message(self, c, u, msg):
        try:
            data = json.loads(msg.payload.decode("utf-8", "replace"))
        except ValueError:
            return
        piece = data.get("print")
        if isinstance(piece, dict):
            with self.lock:
                if piece.get("msg") == 0:
                    self.full_seen = True
                self.state.update(piece)
            self.q.put(("state", None))
            # 命令回执也走 print 这个通道, 以前漏了 —— 所以按了按钮看不到结果
            cmd = piece.get("command")
            if cmd and cmd != "push_status":
                self.q.put(("cmd_reply", ("print", piece)))
        if isinstance(data.get("info"), dict) and data["info"].get("module"):
            with self.lock:
                self.version = data["info"]
            self.q.put(("version", None))
        # 命令回执
        for key in ("system", "camera", "upgrade", "xcam"):
            if isinstance(data.get(key), dict):
                self.q.put(("cmd_reply", (key, data[key])))

    def start(self):
        if mqtt is None:
            self.q.put(("conn", "缺 paho-mqtt"))
            return False
        try:
            client = mqtt.Client(mqtt.CallbackAPIVersion.VERSION2,
                                 client_id="xiaocai-dash", protocol=mqtt.MQTTv311)
        except (AttributeError, TypeError):
            client = mqtt.Client(client_id="xiaocai-dash", protocol=mqtt.MQTTv311)
        client.on_connect = self._on_connect
        client.on_disconnect = self._on_disconnect
        client.on_message = self._on_message
        client.username_pw_set("bblp", self.code)
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        client.tls_set_context(ctx)
        client.tls_insecure_set(True)
        client.reconnect_delay_set(min_delay=2, max_delay=15)
        self.client = client
        try:
            client.connect_async(self.host, 8883, keepalive=30)
            client.loop_start()
            return True
        except Exception:
            log_exc("mqtt start")
            self.q.put(("conn", "连不上 %s:8883" % self.host))
            return False

    def snapshot(self):
        with self.lock:
            return dict(self.state)

    def stop(self):
        if self.client:
            try:
                self.client.loop_stop()
                self.client.disconnect()
            except Exception:
                pass

    # ---- 命令 ----
    def set_light(self, mode):
        return self.send({"system": {"sequence_id": self._next_seq(), "command": "ledctrl",
                                     "led_node": "chamber_light", "led_mode": mode,
                                     "led_on_time": 500, "led_off_time": 500,
                                     "loop_times": 0, "interval_time": 0}},
                         "灯光 -> " + mode)

    def pause(self):
        return self.send({"print": {"sequence_id": self._next_seq(), "command": "pause",
                                    "param": ""}}, "暂停打印")

    def resume(self):
        return self.send({"print": {"sequence_id": self._next_seq(), "command": "resume",
                                    "param": ""}}, "继续打印")

    def stop_print(self):
        return self.send({"print": {"sequence_id": self._next_seq(), "command": "stop",
                                    "param": ""}}, "停止打印")

    def set_speed(self, lvl):
        return self.send({"print": {"sequence_id": self._next_seq(), "command": "print_speed",
                                    "param": str(lvl)}}, "速度档 -> %s" % SPEED_CN.get(lvl, lvl))

    def skip_objects(self, ids):
        return self.send({"print": {"sequence_id": self._next_seq(), "command": "skip_objects",
                                    "obj_list": list(ids)}}, "跳过零件 %s" % ids)

    def timelapse(self, on):
        return self.send({"camera": {"sequence_id": self._next_seq(), "command": "ipcam_timelapse",
                                     "control": "enable" if on else "disable"}},
                         "延时摄影 -> %s" % ("开" if on else "关"))

    def record(self, on):
        return self.send({"camera": {"sequence_id": self._next_seq(), "command": "ipcam_record_set",
                                     "control": "enable" if on else "disable"}},
                         "录像 -> %s" % ("开" if on else "关"))

    def get_access_code(self):
        return self.send({"system": {"sequence_id": self._next_seq(),
                                     "command": "get_access_code"}}, "读取访问码")


# --------------------------------------------------------------------------- #
#  摄像头
# --------------------------------------------------------------------------- #
class CamLink(threading.Thread):
    def __init__(self, host, code, q):
        super().__init__(daemon=True)
        self.host = host
        self.code = code
        self.q = q
        self._stop = threading.Event()
        self.frames = 0
        self.last_jpeg = None
        self.last_t = 0.0
        self.lock = threading.Lock()

    def stop(self):
        self._stop.set()

    @staticmethod
    def _auth(user, code):
        return (struct.pack("<IIII", 0x40, 0x3000, 0, 0)
                + user.encode("ascii").ljust(32, b"\x00")
                + code.encode("ascii").ljust(32, b"\x00"))

    def run(self):
        backoff = 2
        conn_no = 0
        while not self._stop.is_set():
            sock = None
            try:
                ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
                ctx.check_hostname = False
                ctx.verify_mode = ssl.CERT_NONE
                raw = socket.create_connection((self.host, 6000), timeout=6)
                sock = ctx.wrap_socket(raw, server_hostname=self.host)
                sock.settimeout(8)
                sock.sendall(self._auth("bblp", self.code))
                conn_no += 1
                log("摄像头第 %d 次连上了" % conn_no)
                self.q.put(("cam_conn", True))
                backoff = 2
                buf = b""
                t_conn = time.time()
                while not self._stop.is_set():
                    try:
                        chunk = sock.recv(16384)
                    except socket.timeout:
                        continue
                    if not chunk:
                        raise OSError("服务器主动关闭了连接")
                    buf += chunk
                    while len(buf) >= 16:
                        size = struct.unpack("<I", buf[:4])[0]
                        if size <= 0 or size > 8 * 1024 * 1024:
                            buf = buf[1:]
                            continue
                        if len(buf) < 16 + size:
                            break
                        payload = buf[16:16 + size]
                        buf = buf[16 + size:]
                        if payload[:2] != b"\xff\xd8":
                            continue
                        with self.lock:
                            self.last_jpeg = payload
                            self.last_t = time.time()
                        self.frames += 1
                        if self.frames % 30 == 1:
                            log("摄像头第 %d 帧 (这次连了 %.0f 秒)" % (self.frames, time.time() - t_conn))
                        if Image is not None:
                            try:
                                im = Image.open(io.BytesIO(payload))
                                im.load()
                                thumb = im.convert("RGB").resize((CAM_W, CAM_H), Image.LANCZOS)
                            except Exception:
                                continue
                            self.q.put(("cam", (thumb, self.frames)))
            except Exception as exc:
                if not self._stop.is_set():
                    log("摄像头断了(第 %d 次): %s: %s" % (conn_no, type(exc).__name__, exc))
                    self.q.put(("cam_conn", False))
            finally:
                if sock is not None:
                    try:
                        sock.close()
                    except Exception:
                        pass
            if self._stop.is_set():
                break
            for _ in range(int(backoff * 10)):
                if self._stop.is_set():
                    break
                time.sleep(0.1)
            backoff = min(backoff * 2, 30)
        log("摄像头线程退出 (共 %d 帧)" % self.frames)

    def grab_jpeg(self):
        with self.lock:
            return self.last_jpeg

    def age(self):
        """最近一帧是几秒前。没收到过返回 -1。"""
        with self.lock:
            return (time.time() - self.last_t) if self.last_t else -1.0


# --------------------------------------------------------------------------- #
#  FTP（打印机内部文件）
# --------------------------------------------------------------------------- #
class ImplicitFTP(ftplib.FTP_TLS):
    """990 是 implicit FTPS（一上来就 TLS），标准库只支持 AUTH TLS。"""

    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self._sock = None

    @property
    def sock(self):
        return self._sock

    @sock.setter
    def sock(self, value):
        if value is not None and not isinstance(value, ssl.SSLSocket):
            value = self.context.wrap_socket(value)
        self._sock = value


class PrinterFiles:
    """打印机文件访问。所有方法都在后台线程调用。"""

    def __init__(self, host, code, q):
        self.host = host
        self.code = code
        self.q = q
        self.lock = threading.Lock()
        self.f = None

    def _conn(self):
        if self.f is not None:
            try:
                self.f.voidcmd("NOOP")
                return self.f
            except Exception:
                try:
                    self.f.close()
                except Exception:
                    pass
                self.f = None
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        f = ImplicitFTP(context=ctx)
        f.connect(self.host, 990, timeout=15)
        f.login("bblp", self.code)
        try:
            f.prot_p()
        except Exception:
            pass
        f.set_pasv(True)
        self.f = f
        return f

    def close(self):
        with self.lock:
            if self.f:
                try:
                    self.f.close()
                except Exception:
                    pass
                self.f = None

    def list_dir(self, path):
        """返回 [(名字, 字节, 日期串, 是否目录)]"""
        with self.lock:
            f = self._conn()
            f.cwd(path)
            raw = []
            f.retrlines("LIST", raw.append)
        out = []
        for e in raw:
            p = e.split(None, 8)
            if len(p) < 9:
                continue
            name = p[8].strip()
            if name in (".", ".."):
                continue
            try:
                size = int(p[4])
            except ValueError:
                size = 0
            out.append((name, size, "%s %s %s" % (p[5], p[6], p[7]), p[0].startswith("d")))
        return out

    def dir_size(self, path):
        with self.lock:
            f = self._conn()
            f.cwd(path)
            raw = []
            f.retrlines("LIST", raw.append)
        total = 0
        nfiles = 0
        for e in raw:
            p = e.split(None, 8)
            if len(p) < 9 or p[0].startswith("d"):
                continue
            try:
                total += int(p[4])
                nfiles += 1
            except ValueError:
                pass
        return total, nfiles

    def download(self, remote_dir, name, local_path, progress=None):
        os.makedirs(os.path.dirname(local_path), exist_ok=True)
        with self.lock:
            f = self._conn()
            f.cwd(remote_dir)
            try:
                total = f.size(name)
            except Exception:
                total = 0
            done = [0]
            last = [0.0]

            def cb(chunk):
                fh.write(chunk)
                done[0] += len(chunk)
                if progress:
                    now = time.time()
                    if now - last[0] > 0.5:
                        last[0] = now
                        progress(done[0], total)

            with open(local_path, "wb") as fh:
                f.retrbinary("RETR " + name, cb)
        return os.path.getsize(local_path)

    def read_bytes(self, remote_dir, name):
        with self.lock:
            f = self._conn()
            f.cwd(remote_dir)
            buf = bytearray()
            f.retrbinary("RETR " + name, buf.extend)
        return bytes(buf)

    def delete(self, remote_dir, name):
        with self.lock:
            f = self._conn()
            f.cwd(remote_dir)
            f.delete(name)


# --------------------------------------------------------------------------- #
#  界面
# --------------------------------------------------------------------------- #
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Bambu Lab 看板")
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        w, h = min(1240, sw - 50), min(880, sh - 80)
        self.geometry("%dx%d+%d+%d" % (w, h, max(0, (sw - w) // 2), max(0, (sh - h) // 4)))
        self.configure(bg=BG)
        self.minsize(1000, 700)

        self.q = queue.Queue()
        self.link = None
        self.cam = None
        self.files = None
        self.cam_on = False
        self.photo = None
        self.thumb_cache = {}
        self.thumb_photo = None
        self.preview_photo = None
        self.samples = []
        self.last_task = None
        self.last_poll = 0.0
        self.last_state = {}
        self.prev = {}
        self.last_raw_fill = 0.0
        self.cool = CoolModel()
        self.pending = None
        self.reply_count = 0
        self.dir_rows = {}
        self.dir_cache = {}
        self.web = None
        self.web_url = ""
        self.cool_text = ""
        self.want_cam = True
        self.qr_win = None
        self.qr_photo = None
        self.hist_cache = []
        self.hist_loading = False
        self.reply_lines = []
        self.layers = []            # 每层一张位图（bytearray）
        self.layer_bbox = []        # 每层的毫米范围
        self.layer_zh = 0.2         # 层高（从 gcode 头部读）
        self.layer_z0 = 0.2         # 首层高
        self.layer_png_cache = {}
        self.layer_canvas = None
        self.last_layer_drawn = -1
        self.marker_src = tk.StringVar(value="摄像头·蓝标")   # 或 假标记（演示）
        self.toast_n = 0                # 提示小窗的序号（网页靠它判断有没有新提示）
        self.toast = None               # 最近一条提示
        self.toast_wins = []            # 还开着的提示小窗
        self.marker_px = None          # 摄像头里找到的标记（全分辨率像素）
        self.marker_dot = None         # 盘面图上的红点
        self.marker_worker_on = False
        self.marker_target = None      # 锁定跟踪的那个点（像素）
        self.marker_nblobs = 0
        self.marker_blobs = []         # 这一帧找到的所有候选块（给画框用）
        self.last_recog_save = 0.0     # 上次自动存识别图的时间
        self.calib = []                # [((px,py),(x_mm,y_mm)), ...]
        self.affine = None             # 仿射 6 参数
        self.local_H_inv = None        # 本地校准：像素 -> 盘单位坐标 的单应
        self.local_quad = None
        self.plate_edge_y = None       # 盘子前沿在画面里的 y（跟着底盘前后走）
        self.cal_x = None              # (蓝标在 X=0 时的像素x, 在 X=256 时的像素x)
        self.cal_y = None              # (喷嘴在 Y=0 时的前沿像素y, 在 Y=256 时的)
        self.calib_win = None
        self.calib_canvas = None
        self.calib_clicks = []
        self.calib_photo = None
        self.cfg = load_cfg()
        # 上次的本地校准（相机和盘子都不动，标一次一直有效）
        q = self.cfg.get("local_quad")
        if q and len(q) == 4:
            try:
                quad = [tuple(float(v) for v in p) for p in q]
                H = homography_from_quad(quad)
                if H:
                    self.local_H_inv = invert3(H)
                    self.local_quad = quad
                    log("读到上次的本地校准（4 个角）")
            except (TypeError, ValueError):
                log("上次的本地校准数据坏了，忽略")
        # 四步标定（X 看喷头蓝标、Y 看盘子前沿）
        for key in ("cal_x", "cal_y"):
            v = self.cfg.get(key)
            if isinstance(v, (list, tuple)) and len(v) == 2 and all(x is not None for x in v):
                try:
                    setattr(self, key, (float(v[0]), float(v[1])))
                    log("读到上次的 %s: %s" % (key, list(v)))
                except (TypeError, ValueError):
                    pass
        # ⚠️ 这两个要用 cfg, 必须放在 cfg = load_cfg() 之后
        self.var_autolight = tk.BooleanVar(value=bool(self.cfg.get("autolight", True)))
        self.var_lightdelay = tk.StringVar(value=str(self.cfg.get("autolight_delay", 0)))
        self.version_txt = ""
        self.events = []
        self.history = []          # [(名字, 字节, 日期)]
        self.objects = []          # 当前盘里的零件
        self.cur_dir = None
        self.dir_files = []
        self.auto_scroll = tk.BooleanVar(value=True)
        self.sel_history = None

        self.style_ui()
        self.build_ui()
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.report_callback_exception = self.on_tk_error
        self.after(120, self.pump)
        self.after(1000, self.tick)
        self.after(900, self.update_marker)

        # 给平板看的网页（tkinter 窗口没法直接给平板看，所以另开一个网页）
        try:
            self.web = start_web(self)
            ip = local_subnet() or "127.0.0.1"
            self.web_url = "http://%s:%d" % (ip, WEB_PORT)
            log("网页看板: " + self.web_url)
            self.add_event("网页看板开在 " + self.web_url)
            self.after(1500, lambda: self.set_status("平板打开 " + self.web_url))
            self.after(2500, self.save_qr_file)
        except Exception:
            log_exc("start_web")

        serial, code = read_studio_conf()
        if serial:
            self.var_serial.set(serial)
        if code:
            self.var_code.set(code)
        if self.cfg.get("ip"):
            self.var_ip.set(self.cfg["ip"])
        else:
            self.add_event("没存过 IP, 正在自动找打印机…")
            threading.Thread(target=self.auto_find, daemon=True).start()
        if mqtt is None or Image is None:
            miss = []
            if mqtt is None:
                miss.append("paho-mqtt")
            if Image is None:
                miss.append("Pillow")
            self.set_status("缺库: " + ", ".join(miss))
            self.add_event("缺库: " + ", ".join(miss))
        if "--auto" in sys.argv:
            self.after(900, self.auto_start)
        if "--test-autooff" in sys.argv:
            self.after(7000, self.test_autooff)
        for a in sys.argv:
            if a.startswith("--tab="):
                try:
                    idx = int(a.split("=", 1)[1])
                    self.after(1800, lambda i=idx: self.nb.select(i))
                except (ValueError, tk.TclError):
                    pass

    def auto_start(self):
        if self.var_ip.get().strip() and self.var_serial.get().strip() and self.var_code.get().strip():
            self.want_cam = True          # 记住: 断开再连要自动把摄像头开回来
            self.connect_now()            # connect_now 里看到 want_cam 就会开摄像头
        else:
            self.set_status("IP/序列号/访问码没填全")

    # ---------------- 样式 ----------------
    def style_ui(self):
        st = ttk.Style(self)
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure(".", background=BG, foreground=FG, font=(FONT, 10))
        st.configure("TFrame", background=BG)
        st.configure("Card.TFrame", background=CARD)
        st.configure("TLabel", background=BG, foreground=FG, font=(FONT, 10))
        st.configure("Card.TLabel", background=CARD, foreground=FG, font=(FONT, 10))
        st.configure("Dim.Card.TLabel", background=CARD, foreground=DIM, font=(FONT, 9))
        st.configure("Big.Card.TLabel", background=CARD, foreground=FG, font=(MONO, 21, "bold"))
        st.configure("Mid.Card.TLabel", background=CARD, foreground=FG, font=(MONO, 14, "bold"))
        st.configure("Head.Card.TLabel", background=CARD, foreground=ACC, font=(FONT, 11, "bold"))
        st.configure("TButton", font=(FONT, 10), padding=(10, 5), background=CARD2,
                     foreground=FG, borderwidth=0)
        # clam 的默认 active 配色是白底白字, 鼠标一悬停文字就看不见了, 这里改掉
        st.map("TButton",
               background=[("pressed", ACC), ("active", "#2f3b49"), ("disabled", CARD)],
               foreground=[("pressed", "#0b1016"), ("active", FG), ("disabled", "#5a6675")])
        st.map("TNotebook.Tab",
               background=[("selected", CARD2), ("active", "#2a3341")],
               foreground=[("selected", ACC), ("active", FG)])
        st.map("TCheckbutton",
               background=[("active", CARD)], foreground=[("active", ACC)])
        st.configure("TEntry", fieldbackground=CARD2, foreground=FG, insertcolor=FG)
        st.configure("TCheckbutton", background=CARD, foreground=FG, font=(FONT, 9))
        st.map("TCheckbutton", background=[("active", CARD)])
        st.configure("TProgressbar", background=ACC, troughcolor=CARD2, bordercolor=CARD2,
                     lightcolor=ACC, darkcolor=ACC, thickness=18)
        st.configure("Treeview", background=CARD2, fieldbackground=CARD2, foreground=FG,
                     rowheight=23, font=(FONT, 9), borderwidth=0)
        st.configure("Treeview.Heading", background=CARD, foreground=ACC,
                     font=(FONT, 9, "bold"), relief="flat")
        st.map("Treeview", background=[("selected", ACC)], foreground=[("selected", "#0b1016")])
        st.map("Treeview.Heading", background=[("active", CARD2)])
        st.configure("TNotebook", background=BG, borderwidth=0, tabmargins=(2, 4, 2, 0))
        st.configure("TNotebook.Tab", background=CARD, foreground=DIM, padding=(16, 7),
                     font=(FONT, 10))
        st.map("TNotebook.Tab", background=[("selected", CARD2)], foreground=[("selected", ACC)])
        st.configure("Vertical.TScrollbar", background=CARD2, troughcolor=BG, borderwidth=0,
                     arrowcolor=DIM)

    def card(self, parent, title=None, **kw):
        f = ttk.Frame(parent, style="Card.TFrame", padding=12, **kw)
        if title:
            ttk.Label(f, text=title, style="Head.Card.TLabel").pack(anchor="w", pady=(0, 6))
        return f

    # ---------------- 布局 ----------------
    def build_ui(self):
        bar = ttk.Frame(self, padding=(12, 10, 12, 4))
        bar.pack(fill="x")
        ttk.Label(bar, text="IP").pack(side="left")
        self.var_ip = tk.StringVar()
        ttk.Entry(bar, textvariable=self.var_ip, width=15).pack(side="left", padx=(5, 10))
        ttk.Label(bar, text="序列号").pack(side="left")
        self.var_serial = tk.StringVar()
        ttk.Entry(bar, textvariable=self.var_serial, width=19).pack(side="left", padx=(5, 10))
        ttk.Label(bar, text="访问码").pack(side="left")
        self.var_code = tk.StringVar()
        self.ent_code = ttk.Entry(bar, textvariable=self.var_code, width=11, show="*")
        self.ent_code.pack(side="left", padx=(5, 4))
        self.var_show = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar, text="显示", variable=self.var_show,
                        command=self.toggle_show).pack(side="left", padx=(0, 10))
        self.btn_conn = ttk.Button(bar, text="连接", command=self.toggle_conn)
        self.btn_conn.pack(side="left")
        ttk.Button(bar, text="找打印机", command=self.find_now).pack(side="left", padx=6)
        ttk.Button(bar, text="平板二维码", command=self.show_qr).pack(side="left", padx=6)
        self.lbl_conn = ttk.Label(bar, text="未连接", foreground=DIM)
        self.lbl_conn.pack(side="right")

        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=12, pady=(6, 4))
        self.tab_dash = ttk.Frame(self.nb, padding=10)
        self.tab_layer = ttk.Frame(self.nb, padding=10)
        self.tab_hist = ttk.Frame(self.nb, padding=10)
        self.tab_log = ttk.Frame(self.nb, padding=10)
        self.tab_ctrl = ttk.Frame(self.nb, padding=10)
        self.tab_disk = ttk.Frame(self.nb, padding=10)
        self.tab_raw = ttk.Frame(self.nb, padding=10)
        self.nb.add(self.tab_dash, text="看板")
        self.nb.add(self.tab_layer, text="层图")
        self.nb.add(self.tab_hist, text="打印历史")
        self.nb.add(self.tab_log, text="事件流水")
        self.nb.add(self.tab_ctrl, text="控制")
        self.nb.add(self.tab_disk, text="打印机存储")
        self.nb.add(self.tab_raw, text="全部字段")
        self.nb.bind("<<NotebookTabChanged>>", self.on_tab)

        self.build_dash(self.tab_dash)
        self.build_layer(self.tab_layer)
        self.build_hist(self.tab_hist)
        self.build_log(self.tab_log)
        self.build_ctrl(self.tab_ctrl)
        self.build_disk(self.tab_disk)
        self.build_raw(self.tab_raw)

        self.lbl_status = ttk.Label(self, text="就绪", foreground=DIM, padding=(14, 0, 14, 8))
        self.lbl_status.pack(fill="x")

    # ---- 看板 ----
    def build_dash(self, root):
        root.columnconfigure(0, weight=3)
        root.columnconfigure(1, weight=2)
        root.rowconfigure(0, weight=1)
        left = ttk.Frame(root)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        right = ttk.Frame(root)
        right.grid(row=0, column=1, sticky="nsew")

        f = self.card(left, "打印状态")
        f.pack(fill="x")
        row = ttk.Frame(f, style="Card.TFrame")
        row.pack(fill="x")
        self.lbl_state = ttk.Label(row, text="—", style="Big.Card.TLabel", foreground=ACC)
        self.lbl_state.pack(side="left")
        self.lbl_speed = ttk.Label(row, text="", style="Dim.Card.TLabel")
        self.lbl_speed.pack(side="left", padx=(12, 0), pady=(8, 0))
        self.lbl_stage = ttk.Label(row, text="", style="Card.TLabel", foreground=WARN)
        self.lbl_stage.pack(side="left", padx=(14, 0), pady=(8, 0))
        self.lbl_task = ttk.Label(row, text="", style="Card.TLabel")
        self.lbl_task.pack(side="right", pady=(8, 0))
        self.pb = ttk.Progressbar(f, maximum=100)
        self.pb.pack(fill="x", pady=(8, 4))
        info = ttk.Frame(f, style="Card.TFrame")
        info.pack(fill="x")
        self.lbl_pct = ttk.Label(info, text="—", style="Mid.Card.TLabel")
        self.lbl_pct.pack(side="left")
        self.lbl_left = ttk.Label(info, text="", style="Card.TLabel")
        self.lbl_left.pack(side="left", padx=(14, 0))
        self.lbl_layer = ttk.Label(info, text="", style="Card.TLabel")
        self.lbl_layer.pack(side="right")
        self.lbl_file = ttk.Label(f, text="文件: —", style="Card.TLabel",
                                  wraplength=540, justify="left")
        self.lbl_file.pack(anchor="w", pady=(8, 0))
        self.lbl_weight = ttk.Label(f, text="", style="Dim.Card.TLabel")
        self.lbl_weight.pack(anchor="w", pady=(6, 0))

        f2 = self.card(left, "温度")
        f2.pack(fill="both", expand=True, pady=(10, 0))
        tgrid = ttk.Frame(f2, style="Card.TFrame")
        tgrid.pack(fill="x")
        self.lbl_nozzle = self.temp_cell(tgrid, 0, "喷嘴", HOT)
        self.lbl_bed = self.temp_cell(tgrid, 1, "热床", COOL)
        self.lbl_cham = self.temp_cell(tgrid, 2, "腔温", DIM)
        self.lbl_cool = ttk.Label(f2, text="冷却估计: 还在采数据…", style="Card.TLabel",
                                  wraplength=430, justify="left")
        self.lbl_cool.pack(anchor="w", pady=(8, 0))
        self.chart = tk.Canvas(f2, width=CHART_W, height=CHART_H, bg=CARD, highlightthickness=0)
        self.chart.pack(fill="both", expand=True, pady=(10, 0))

        f3 = self.card(right, "摄像头")
        f3.pack(fill="both", expand=True)
        cb = ttk.Frame(f3, style="Card.TFrame")
        cb.pack(fill="x")
        self.btn_cam = ttk.Button(cb, text="开摄像头", command=self.toggle_cam)
        self.btn_cam.pack(side="left")
        ttk.Button(cb, text="存一张", command=self.save_shot).pack(side="left", padx=6)
        ttk.Button(cb, text="存识别图", command=self.save_recog_shot).pack(side="left")
        self.lbl_cam = ttk.Label(cb, text="", style="Dim.Card.TLabel")
        self.lbl_cam.pack(side="right")
        self.canvas_cam = tk.Canvas(f3, width=CAM_W, height=CAM_H, bg="#0a0d11",
                                    highlightthickness=0)
        self.canvas_cam.pack(pady=(10, 0))
        self.canvas_cam.bind("<Button-1>", self.on_cam_click)
        self.cam_img_id = self.canvas_cam.create_text(CAM_W // 2, CAM_H // 2,
                                                      text="摄像头没开", fill=DIM, font=(FONT, 11))
        self.lbl_cam_status = ttk.Label(f3, text="识别：还没开摄像头", style="Dim.Card.TLabel",
                                        wraplength=CAM_W, justify="left")
        self.lbl_cam_status.pack(anchor="w", pady=(6, 0))

        f4 = self.card(root, "耗材 / 风扇 / 其它")
        f4.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        grid = ttk.Frame(f4, style="Card.TFrame")
        grid.pack(fill="x")
        self.swatch = tk.Canvas(grid, width=14, height=14, bg=CARD, highlightthickness=1,
                                highlightbackground="#3a4553")
        self.swatch.grid(row=0, column=0, sticky="w", padx=(0, 6))
        self.swatch_id = self.swatch.create_rectangle(0, 0, 14, 14, fill="#ffffff", outline="")
        self.lbl_fil = ttk.Label(grid, text="耗材: —", style="Card.TLabel")
        self.lbl_fil.grid(row=0, column=1, sticky="w", padx=(0, 22))
        self.lbl_fan = ttk.Label(grid, text="风扇: —", style="Card.TLabel")
        self.lbl_fan.grid(row=0, column=2, sticky="w", padx=(0, 22))
        self.lbl_wifi = ttk.Label(grid, text="WiFi: —", style="Card.TLabel")
        self.lbl_wifi.grid(row=0, column=3, sticky="w", padx=(0, 22))
        self.lbl_misc = ttk.Label(grid, text="", style="Card.TLabel")
        self.lbl_misc.grid(row=0, column=4, sticky="w")
        self.lbl_hms = ttk.Label(f4, text="健康: —", style="Dim.Card.TLabel")
        self.lbl_hms.pack(anchor="w", pady=(6, 0))
        self.lbl_ver = ttk.Label(f4, text="", style="Dim.Card.TLabel")
        self.lbl_ver.pack(anchor="w")

    def temp_cell(self, parent, col, name, color):
        f = ttk.Frame(parent, style="Card.TFrame")
        f.grid(row=0, column=col, sticky="w", padx=(0, 30))
        ttk.Label(f, text=name, style="Dim.Card.TLabel").pack(anchor="w")
        big = ttk.Label(f, text="—", style="Big.Card.TLabel", foreground=color)
        big.pack(anchor="w")
        sub = ttk.Label(f, text="", style="Dim.Card.TLabel")
        sub.pack(anchor="w")
        big.sub = sub
        return big

    # ---- 层图 ----
    def build_layer(self, root):
        root.columnconfigure(0, weight=1)
        root.rowconfigure(1, weight=1)
        top = ttk.Frame(root)
        top.grid(row=0, column=0, sticky="ew")
        self.lbl_layer_big = ttk.Label(top, text="等开始打印后会自动算出来", style="TLabel")
        self.lbl_layer_big.pack(anchor="w")
        ttk.Label(top, text="左下角是原点 (0,0)，X 往右、Y 往后　青色 = 这一层要挤出的地方　"
                            "橙框 = 范围　红点 = 喷头位置　（层图从 3mf 的 gcode 算，不用标定）\n"
                            "⚠️ 红点的位置是纯靠画面数据估算的：贴纸比喷嘴高几厘米，有视差，"
                            "标定也是手工记的 —— 可能不准，只当参考",
                  foreground=DIM, wraplength=1100).pack(anchor="w", pady=(4, 6))
        ctl = ttk.Frame(top)
        ctl.pack(anchor="w", pady=(0, 4))
        ttk.Label(ctl, text="标记来源").pack(side="left")
        self.cmb_marker = ttk.Combobox(ctl, state="readonly", width=15,
                                       textvariable=self.marker_src,
                                       values=("假标记（演示）", "摄像头·蓝标"))
        self.cmb_marker.pack(side="left", padx=6)
        self.cmb_marker.bind("<<ComboboxSelected>>", lambda _e: self.set_marker_src())
        ttk.Button(ctl, text="用当前标记记一个点", command=self.record_calib).pack(side="left", padx=6)
        ttk.Button(ctl, text="本地校准（点盘的4个角）", command=self.open_calib_window).pack(side="left")
        ttk.Button(ctl, text="看 4 个角", command=self.show_quad).pack(side="left", padx=6)
        ttk.Button(ctl, text="前后对调", command=lambda: self.flip_quad("y")).pack(side="left")
        ttk.Button(ctl, text="左右对调", command=lambda: self.flip_quad("x")).pack(side="left", padx=6)
        ttk.Button(ctl, text="清空标定", command=self.reset_calib).pack(side="left")
        ctl2 = ttk.Frame(top)
        ctl2.pack(anchor="w", pady=(0, 4))
        ttk.Label(ctl2, text="四角标定（把喷嘴开到盘子的角上，再点对应的按钮）:").pack(side="left")
        ttk.Button(ctl2, text="喷嘴在盘左前",
                   command=lambda: self.record_corner("左前", 0, 0)).pack(side="left", padx=(8, 4))
        ttk.Button(ctl2, text="喷嘴在盘左后",
                   command=lambda: self.record_corner("左后", 0, 256)).pack(side="left")
        ttk.Button(ctl2, text="喷嘴在盘右前",
                   command=lambda: self.record_corner("右前", 256, 0)).pack(side="left", padx=(8, 4))
        ttk.Button(ctl2, text="喷嘴在盘右后",
                   command=lambda: self.record_corner("右后", 256, 256)).pack(side="left")
        self.lbl_marker = ttk.Label(top, text="", foreground=WARN, wraplength=1100,
                                    justify="left")
        self.lbl_marker.pack(anchor="w", pady=(0, 6))
        self.layer_canvas = tk.Canvas(root, width=LAYER_PX, height=LAYER_PX, bg="#12161c",
                                      highlightthickness=1, highlightbackground="#39434f")
        self.layer_canvas.grid(row=1, column=0, sticky="nsew")

    # ---- 打印历史 ----
    def build_hist(self, root):
        root.columnconfigure(0, weight=3)
        root.columnconfigure(1, weight=2)
        root.rowconfigure(1, weight=1)
        top = ttk.Frame(root)
        top.grid(row=0, column=0, columnspan=2, sticky="ew")
        ttk.Button(top, text="刷新列表", command=self.load_history).pack(side="left")
        ttk.Button(top, text="下载选中的视频", command=self.dl_selected_video).pack(side="left", padx=6)
        ttk.Button(top, text="下载全部视频", command=self.dl_all_videos).pack(side="left")
        ttk.Button(top, text="打开下载文件夹", command=self.open_dl_folder).pack(side="left", padx=6)
        self.lbl_hist = ttk.Label(top, text="点「刷新列表」去打印机取数据", foreground=DIM)
        self.lbl_hist.pack(side="right")

        box = self.card(root, "每一次打印（延时摄影目录里一段，名字就是打印开始的时间）")
        box.grid(row=1, column=0, sticky="nsew", pady=(8, 0), padx=(0, 10))
        cols = ("时间", "大小", "文件")
        self.tree_hist = ttk.Treeview(box, columns=cols, show="headings", selectmode="browse")
        for c, wd in zip(cols, (150, 90, 300)):
            self.tree_hist.heading(c, text=c)
            self.tree_hist.column(c, width=wd, anchor="w")
        self.tree_hist.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(box, orient="vertical", command=self.tree_hist.yview)
        sb.pack(side="right", fill="y")
        self.tree_hist.configure(yscrollcommand=sb.set)
        self.tree_hist.bind("<<TreeviewSelect>>", self.on_hist_select)

        pv = self.card(root, "这一盘的封面（打完那一刻拍的）")
        pv.grid(row=1, column=1, sticky="nsew", pady=(8, 0))
        self.canvas_hist = tk.Canvas(pv, width=THUMB_W, height=THUMB_H, bg="#0a0d11",
                                     highlightthickness=0)
        self.canvas_hist.pack()
        self.hist_text = tk.Text(pv, height=8, bg=CARD2, fg=FG, insertbackground=FG,
                                 font=(MONO, 9), relief="flat", wrap="word")
        self.hist_text.pack(fill="both", expand=True, pady=(10, 0))
        self.hist_text.configure(state="disabled")

    # ---- 事件流水 ----
    def build_log(self, root):
        root.rowconfigure(1, weight=1)
        root.columnconfigure(0, weight=1)
        top = ttk.Frame(root)
        top.grid(row=0, column=0, sticky="ew")
        ttk.Button(top, text="清空", command=self.clear_events).pack(side="left")
        ttk.Button(top, text="保存成文件", command=self.save_events).pack(side="left", padx=6)
        ttk.Checkbutton(top, text="自动滚到底", variable=self.auto_scroll).pack(side="left", padx=6)
        ttk.Label(top, text="过滤").pack(side="left", padx=(16, 4))
        self.var_filter = tk.StringVar()
        ttk.Entry(top, textvariable=self.var_filter, width=18).pack(side="left")
        ttk.Button(top, text="应用过滤", command=self.render_events).pack(side="left", padx=6)
        self.lbl_log_n = ttk.Label(top, text="", foreground=DIM)
        self.lbl_log_n.pack(side="right")

        box = self.card(root, "看板记录的事件（打印机内部的 mc_print 日志这台 A1 不往外推，"
                              "内部 log 文件是加密的，所以这里记的是状态变化 + 指令往来）")
        box.grid(row=1, column=0, sticky="nsew", pady=(8, 0))
        self.txt_log = tk.Text(box, bg="#0e1218", fg=FG, insertbackground=FG, font=(MONO, 9),
                               relief="flat", wrap="none")
        self.txt_log.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(box, orient="vertical", command=self.txt_log.yview)
        sb.pack(side="right", fill="y")
        self.txt_log.configure(yscrollcommand=sb.set, state="disabled")

    # ---- 控制 ----
    def build_ctrl(self, root):
        root.columnconfigure(0, weight=1)
        root.columnconfigure(1, weight=1)
        f1 = self.card(root, "打印控制")
        f1.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        self.lbl_ctrl_state = ttk.Label(f1, text="—", style="Mid.Card.TLabel")
        self.lbl_ctrl_state.pack(anchor="w", pady=(0, 4))
        self.lbl_ctrl_note = ttk.Label(f1, text="", style="Dim.Card.TLabel",
                                       wraplength=380, justify="left")
        self.lbl_ctrl_note.pack(anchor="w", pady=(0, 8))
        r1 = ttk.Frame(f1, style="Card.TFrame")
        r1.pack(fill="x")
        self.btn_pause = ttk.Button(r1, text="暂停", command=self.do_pause)
        self.btn_pause.pack(side="left")
        self.btn_resume = ttk.Button(r1, text="继续", command=self.do_resume)
        self.btn_resume.pack(side="left", padx=6)
        self.btn_stop = ttk.Button(r1, text="停止打印", command=self.do_stop)
        self.btn_stop.pack(side="left")
        ttk.Label(f1, text="速度档位", style="Dim.Card.TLabel").pack(anchor="w", pady=(12, 4))
        r2 = ttk.Frame(f1, style="Card.TFrame")
        r2.pack(fill="x")
        self.speed_btns = {}
        for lvl in (1, 2, 3, 4):
            b = ttk.Button(r2, text=SPEED_CN[lvl], command=lambda L=lvl: self.do_speed(L))
            b.pack(side="left", padx=(0, 6))
            self.speed_btns[lvl] = b
        ttk.Label(f1, text="灯光", style="Dim.Card.TLabel").pack(anchor="w", pady=(12, 4))
        r3 = ttk.Frame(f1, style="Card.TFrame")
        r3.pack(fill="x")
        ttk.Button(r3, text="开", command=lambda: self.do_light("on")).pack(side="left")
        ttk.Button(r3, text="关", command=lambda: self.do_light("off")).pack(side="left", padx=6)
        ttk.Button(r3, text="闪", command=lambda: self.do_light("flashing")).pack(side="left")
        r3b = ttk.Frame(f1, style="Card.TFrame")
        r3b.pack(fill="x", pady=(6, 0))
        ttk.Checkbutton(r3b, text="打完后自动关灯", variable=self.var_autolight,
                        command=self.save_light_opts).pack(side="left")
        ttk.Label(r3b, text="延迟(秒)", style="Dim.Card.TLabel").pack(side="left", padx=(12, 4))
        ent = ttk.Entry(r3b, textvariable=self.var_lightdelay, width=5)
        ent.pack(side="left")
        ent.bind("<FocusOut>", lambda _e: self.save_light_opts())
        ent.bind("<Return>", lambda _e: self.save_light_opts())
        ttk.Label(f1, text="闪：实测这台 A1 不支持 —— 发过去打印机回 success，但灯不动、"
                           "状态里也一直报 off",
                  style="Dim.Card.TLabel", wraplength=380, justify="left").pack(anchor="w",
                                                                                 pady=(4, 0))

        f2 = self.card(root, "摄像 / 录像")
        f2.grid(row=0, column=1, sticky="nsew")
        self.btn_tl = ttk.Button(f2, text="延时摄影: ?", command=self.do_toggle_timelapse)
        self.btn_tl.pack(anchor="w")
        self.btn_rec = ttk.Button(f2, text="录像: ?", command=self.do_toggle_record)
        self.btn_rec.pack(anchor="w", pady=6)
        ttk.Label(f2, text="录像很占地方（你卡里已经 14.6 GB），关了就不再涨",
                  style="Dim.Card.TLabel").pack(anchor="w")

        f3 = self.card(root, "跳过零件（一盘打了多个件时，单独取消一个）")
        f3.grid(row=1, column=0, columnspan=2, sticky="nsew", pady=(10, 0))
        r4 = ttk.Frame(f3, style="Card.TFrame")
        r4.pack(fill="x")
        ttk.Button(r4, text="读取当前盘的零件清单", command=self.load_objects).pack(side="left")
        ttk.Button(r4, text="跳过选中的零件", command=self.do_skip).pack(side="left", padx=6)
        self.lbl_obj = ttk.Label(r4, text="", style="Dim.Card.TLabel")
        self.lbl_obj.pack(side="left", padx=10)
        cols = ("id", "零件名", "状态")
        self.tree_obj = ttk.Treeview(f3, columns=cols, show="headings", height=6, selectmode="extended")
        for c, wd in zip(cols, (70, 420, 110)):
            self.tree_obj.heading(c, text=c)
            self.tree_obj.column(c, width=wd, anchor="w")
        self.tree_obj.pack(fill="both", expand=True, pady=(8, 0))

        f4 = self.card(root, "指令回执（打印机怎么回的）")
        f4.grid(row=2, column=0, columnspan=2, sticky="nsew", pady=(10, 0))
        self.txt_reply = tk.Text(f4, height=6, bg=CARD2, fg=FG, font=(MONO, 9), relief="flat",
                                 wrap="word")
        self.txt_reply.pack(fill="both", expand=True)
        self.txt_reply.configure(state="disabled")

    # ---- 存储 ----
    def build_disk(self, root):
        root.columnconfigure(0, weight=1)
        root.rowconfigure(2, weight=1)
        top = ttk.Frame(root)
        top.grid(row=0, column=0, sticky="ew")
        ttk.Button(top, text="下载选中文件", command=self.dl_selected_files).pack(side="left")
        ttk.Button(top, text="删除选中文件", command=self.del_selected_files).pack(side="left", padx=6)
        ttk.Button(top, text="打开下载文件夹", command=self.open_dl_folder).pack(side="left")
        ttk.Button(top, text="统计全部（慢）", command=self.load_disk).pack(side="left", padx=6)
        self.lbl_disk = ttk.Label(top, text="点哪个目录才去读哪个，不会一次全读",
                                  foreground=DIM)
        self.lbl_disk.pack(side="right")

        box1 = self.card(root, "打印机内部存储")
        box1.grid(row=1, column=0, sticky="ew", pady=(8, 0))
        cols = ("目录", "里面是什么", "文件数", "占用")
        self.tree_disk = ttk.Treeview(box1, columns=cols, show="headings", height=7,
                                      selectmode="browse")
        for c, wd in zip(cols, (140, 420, 90, 110)):
            self.tree_disk.heading(c, text=c)
            self.tree_disk.column(c, width=wd, anchor="w")
        self.tree_disk.pack(fill="x")
        self.tree_disk.bind("<<TreeviewSelect>>", self.on_dir_select)
        self.show_disk_rows()

        box2 = self.card(root, "目录里的文件（下载会存到「打印机下载」文件夹）")
        box2.grid(row=2, column=0, sticky="nsew", pady=(10, 0))
        cols2 = ("文件名", "大小", "日期")
        self.tree_files = ttk.Treeview(box2, columns=cols2, show="headings", selectmode="extended")
        for c, wd in zip(cols2, (420, 110, 200)):
            self.tree_files.heading(c, text=c)
            self.tree_files.column(c, width=wd, anchor="w")
        self.tree_files.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(box2, orient="vertical", command=self.tree_files.yview)
        sb.pack(side="right", fill="y")
        self.tree_files.configure(yscrollcommand=sb.set)

    # ---- 全部字段 ----
    def build_raw(self, root):
        root.rowconfigure(0, weight=1)
        root.columnconfigure(0, weight=1)
        box = self.card(root, "打印机报上来的所有字段（原始值，一帧 60 多个）")
        box.grid(row=0, column=0, sticky="nsew")
        cols = ("字段", "值")
        self.tree_raw = ttk.Treeview(box, columns=cols, show="headings")
        self.tree_raw.heading("字段", text="字段")
        self.tree_raw.heading("值", text="值")
        self.tree_raw.column("字段", width=220, anchor="w")
        self.tree_raw.column("值", width=720, anchor="w")
        self.tree_raw.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(box, orient="vertical", command=self.tree_raw.yview)
        sb.pack(side="right", fill="y")
        self.tree_raw.configure(yscrollcommand=sb.set)

    # ---------------- 小动作 ----------------
    def set_status(self, text):
        self.lbl_status.configure(text=text)

    def add_event(self, text):
        stamp = datetime.datetime.now().strftime("%H:%M:%S")
        self.events.append("%s  %s" % (stamp, text))
        if len(self.events) > 3000:
            self.events = self.events[-3000:]
        self.render_events()

    def notify(self, title, text="", kind="info"):
        """弹一个小提示（桌面小窗 + 事件流水 + 同步给网页）。"""
        try:
            self.toast_n += 1
            self.toast = {"id": self.toast_n, "title": title, "text": text, "kind": kind}
        except Exception:
            pass
        try:
            self.add_event("🔔 " + title + (("　" + text) if text else ""))
        except Exception:
            pass
        self.show_toast(title, text, kind)

    def show_toast(self, title, text, kind="info"):
        """右下角弹一个 7 秒自动消失的小窗。"""
        try:
            w = tk.Toplevel(self)
            w.overrideredirect(True)
            try:
                w.attributes("-topmost", True)
            except tk.TclError:
                pass
            w.configure(bg="#1b2027")
            color = {"info": OK, "warn": WARN, "bad": BAD}.get(kind, OK)
            tk.Label(w, text=title, bg="#1b2027", fg=color,
                     font=("Microsoft YaHei", 12, "bold")).pack(anchor="w", padx=14, pady=(10, 2))
            if text:
                tk.Label(w, text=text, bg="#1b2027", fg="#c9d1d9", justify="left",
                         wraplength=380).pack(anchor="w", padx=14, pady=(0, 10))
            w.update_idletasks()
            sw, sh = w.winfo_screenwidth(), w.winfo_screenheight()
            ww, wh = w.winfo_width(), w.winfo_height()
            w.geometry("+%d+%d" % (max(0, sw - ww - 24), max(0, sh - wh - 64)))
            self.toast_wins.append(w)
            while len(self.toast_wins) > 4:
                old = self.toast_wins.pop(0)
                try:
                    old.destroy()
                except tk.TclError:
                    pass
            w.after(7000, w.destroy)
        except tk.TclError:
            pass

    def render_events(self):
        try:
            want = self.var_filter.get().strip()
            shown = [e for e in self.events if (want in e)] if want else self.events
            self.txt_log.configure(state="normal")
            self.txt_log.delete("1.0", "end")
            self.txt_log.insert("end", "\n".join(shown) + ("\n" if shown else ""))
            self.txt_log.configure(state="disabled")
            if self.auto_scroll.get():
                self.txt_log.see("end")
            self.lbl_log_n.configure(text="共 %d 条" % len(self.events))
        except tk.TclError as exc:
            log("!! render_events: %s" % exc)

    def clear_events(self):
        self.events = []
        self.render_events()

    def save_events(self):
        path = filedialog.asksaveasfilename(defaultextension=".txt",
                                            initialfile="Bambu事件流水.txt",
                                            initialdir=HERE)
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(self.events))
        self.set_status("事件流水已保存: " + path)

    def show_reply(self, key, payload):
        self.reply_count += 1
        self.pending = None
        cmd = payload.get("command", "")
        res = payload.get("result", "")
        reason = payload.get("reason", "")
        self.txt_reply.configure(state="normal")
        self.txt_reply.insert("end", "[%s] %s %s -> %s %s\n" % (
            datetime.datetime.now().strftime("%H:%M:%S"), key, cmd,
            res or "(只回显了命令，没写结果)", reason))
        self.txt_reply.insert("end", "        " + json.dumps(payload, ensure_ascii=False)[:300] + "\n")
        self.txt_reply.see("end")
        self.txt_reply.configure(state="disabled")
        self.set_status("打印机回话: %s %s %s" % (cmd, res, reason))
        self.add_event("回执 %s/%s: %s %s" % (key, cmd, res or "?", reason))
        self.reply_lines.append("%s  %s/%s -> %s %s" % (
            datetime.datetime.now().strftime("%H:%M:%S"), key, cmd,
            res or "(只回显了命令)", reason))
        if len(self.reply_lines) > 200:
            self.reply_lines = self.reply_lines[-200:]
        # 全部落盘 —— 「MQTT 命令校验失败」这种报错就是从这里抓到的
        log("回执 %s/%s: %s" % (key, cmd, json.dumps(payload, ensure_ascii=False)[:500]))

    def note_sent(self, note):
        self.pending = (note, self.reply_count)
        self.set_status("已发出: %s —— 等打印机回话…" % note)
        self.after(5000, self.check_pending)

    def check_pending(self):
        if not self.pending:
            return
        note, cnt = self.pending
        if self.reply_count == cnt:
            self.set_status("「%s」发出去了，但打印机 5 秒内没回话" % note)
            self.add_event("指令没回话: " + note)
            self.pending = None

    def toggle_show(self):
        self.ent_code.configure(show="" if self.var_show.get() else "*")

    def on_tk_error(self, exc, val, tb):
        log("!! 界面出错: %s: %s\n%s" % (exc.__name__, val, "".join(traceback.format_tb(tb))))
        try:
            messagebox.showerror("出错了", "%s: %s" % (exc.__name__, val))
        except Exception:
            pass

    def auto_find(self):
        self.q.put(("found", scan_for_printer(logf=log)))

    def find_now(self):
        self.set_status("正在扫描局域网…")
        threading.Thread(target=self.auto_find, daemon=True).start()

    def on_tab(self, _evt=None):
        try:
            name = self.nb.tab(self.nb.select(), "text")
        except tk.TclError:
            return
        if name == "打印历史" and not self.history:
            self.load_history()
        elif name == "打印机存储" and not self.tree_disk.get_children():
            self.show_disk_rows()

    # ---------------- 连接 ----------------
    def toggle_conn(self):
        if self.link:
            self.disconnect()
        else:
            self.connect_now()

    def connect_now(self):
        ip = self.var_ip.get().strip()
        serial = self.var_serial.get().strip()
        code = self.var_code.get().strip()
        if not (ip and serial and code):
            messagebox.showwarning("差点东西", "IP、序列号、访问码三个都要填。\n"
                                              "访问码在打印机屏幕上: 设置 → 网络 → 访问码")
            return
        self.cfg["ip"] = ip
        self.cfg["serial"] = serial
        save_cfg(self.cfg)
        self.link = PrinterLink(ip, serial, code, self.q)
        self.link.start()
        self.files = PrinterFiles(ip, code, self.q)
        self.btn_conn.configure(text="断开")
        self.lbl_conn.configure(text="连接中…", foreground=WARN)
        self.set_status("正在连 %s …" % ip)
        self.add_event("开始连 %s" % ip)
        if self.want_cam:            # 断开重连时把摄像头自动开回来
            self.start_cam()

    def disconnect(self):
        self.stop_cam()
        if self.link:
            self.link.stop()
        if self.files:
            self.files.close()
        self.link = None
        self.files = None
        self.btn_conn.configure(text="连接")
        self.lbl_conn.configure(text="未连接", foreground=DIM)
        self.set_status("已断开")
        self.add_event("已断开")

    def start_cam(self):
        if not self.link:
            return
        self.stop_cam(keep=True)      # 重启摄像头时别把上一帧画面擦掉
        self.cam = CamLink(self.var_ip.get().strip(), self.var_code.get().strip(), self.q)
        self.cam.start()
        self.cam_on = True
        self.btn_cam.configure(text="关摄像头")
        self.lbl_cam.configure(text="连接中…")
        self.start_marker_worker()      # 摄像头一开就一直识别

    def stop_cam(self, keep=False):
        if self.cam:
            self.cam.stop()
        self.cam = None
        self.marker_worker_on = False
        self.cam_on = False
        self.btn_cam.configure(text="开摄像头")
        self.lbl_cam.configure(text="")
        if not keep:
            self.canvas_cam.delete("frame")
            self.canvas_cam.itemconfigure(self.cam_img_id, state="normal")

    def toggle_cam(self):
        if self.cam_on:
            self.want_cam = False        # 他自己关的, 那就不自动开回来
            self.stop_cam()
        else:
            if not self.link:
                messagebox.showinfo("先连打印机", "先点「连接」，再开摄像头。")
                return
            self.want_cam = True
            self.start_cam()

    def save_shot(self):
        if not self.cam:
            messagebox.showinfo("没画面", "先开摄像头。")
            return
        data = self.cam.grab_jpeg()
        if not data:
            messagebox.showinfo("还没画面", "还没收到画面，再等等。")
            return
        os.makedirs(SHOT_DIR, exist_ok=True)
        path = os.path.join(SHOT_DIR, "截图_%s.jpg" % datetime.datetime.now().strftime("%Y%m%d_%H%M%S"))
        with open(path, "wb") as f:
            f.write(data)
        self.set_status("存好了: " + path)
        self.add_event("存了一张画面: " + os.path.basename(path))

    # ---------------- 队列 ----------------
    def pump(self):
        try:
            while True:
                try:
                    kind, payload = self.q.get_nowait()
                except queue.Empty:
                    break
                try:
                    self.dispatch(kind, payload)
                except tk.TclError as exc:
                    log("!! 处理 %s 界面错误: %s" % (kind, exc))
                except Exception:
                    log_exc("dispatch " + kind)
        finally:
            self.after(120, self.pump)

    def dispatch(self, kind, payload):
        if kind == "state":
            self.refresh()
        elif kind == "version":
            self.show_version()
        elif kind == "conn":
            up = "连上" in str(payload)
            self.lbl_conn.configure(text=str(payload), foreground=OK if up else WARN)
            self.set_status(str(payload))
            if up:
                self.add_event("MQTT 连上了")
                self.notify("设备已开机（打印机连上了）", "现在能收数据了", "info")
            else:
                self.notify("连接丢失！", str(payload) + "　打印机断电了？WiFi 掉了？", "bad")
        elif kind == "found":
            if payload:
                if not self.var_ip.get().strip():
                    self.var_ip.set(payload[0])
                self.set_status("找到 %d 台: %s" % (len(payload), ", ".join(payload)))
                self.add_event("自动找到打印机: " + ", ".join(payload))
            else:
                self.set_status("没扫到打印机 —— 手动填 IP 也行")
        elif kind == "cam":
            thumb, n = payload
            self.show_frame(thumb, n)
        elif kind == "cam_conn":
            self.lbl_cam.configure(text="画面来了" if payload else "重连中…",
                                   foreground=OK if payload else WARN)
            self.add_event("摄像头" + ("接上了" if payload else "断了，重连中"))
            self.notify("摄像头接上了" if payload else "摄像头断了",
                        "画面恢复" if payload else "程序会自动重连，稍等", "info" if payload else "warn")
        elif kind == "event":
            self.add_event(str(payload))
        elif kind == "cmd_reply":
            self.show_reply(*payload)
        elif kind == "cmd_sent":
            self.note_sent(str(payload))
        elif kind == "web_light":
            if self.link:
                self.link.set_light("on" if payload else "off")
        elif kind == "web_cmd":
            self.run_web_cmd(payload)
        elif kind == "web_cal":
            self.run_web_cal(payload)
        elif kind == "layers":
            self.layers, self.layer_bbox, self.layer_zh, self.layer_z0 = payload
            self.layer_png_cache = {}
            self.last_layer_drawn = -1
            self.add_event("层图算好了: %d 层（从 gcode 算的，不用标定）" % len(self.layers))
            self.draw_layer_map()
        elif kind == "auth_bad":
            self.lbl_conn.configure(text="访问码不对", foreground=BAD)
            self.set_status("打印机拒绝了连接（%s）。多半是打印机换了访问码 —— "
                            "在打印机屏幕上打开「设置 → 网络（局域网模式）」，把新的访问码"
                            "填到上面那个框里，再点「连接」。" % payload)
            self.add_event("MQTT 被拒: %s —— 访问码可能换了，去打印机屏幕上看新的" % payload)
        elif kind == "hist":
            self.fill_history(payload)
        elif kind == "thumb":
            self.show_hist_thumb(*payload)
        elif kind == "disk":
            self.fill_disk(payload)
        elif kind == "dirfiles":
            self.fill_dir_files(*payload)
        elif kind == "objects":
            self.fill_objects(*payload)
        elif kind == "dl":
            self.set_status(str(payload))
            self.add_event(str(payload))
        elif kind == "msg":
            self.set_status(str(payload))

    def show_frame(self, thumb, n):
        if ImageTk is None:
            return
        try:
            self.photo = ImageTk.PhotoImage(thumb)
        except Exception:
            log_exc("ImageTk")
            return
        self.canvas_cam.delete("frame")
        self.canvas_cam.delete("mark")
        self.canvas_cam.itemconfigure(self.cam_img_id, state="hidden")
        self.canvas_cam.create_image(0, 0, anchor="nw", image=self.photo, tags="frame")
        if self.marker_px:
            sx = self.marker_px[0] * CAM_W / 1536.0
            sy = self.marker_px[1] * CAM_H / 1080.0
            self.canvas_cam.create_line(sx - 15, sy, sx + 15, sy, fill=BAD, width=3, tags="mark")
            self.canvas_cam.create_line(sx, sy - 15, sx, sy + 15, fill=BAD, width=3, tags="mark")
        if self.plate_edge_y:
            ey = self.plate_edge_y * CAM_H / 1080.0
            self.canvas_cam.create_line(0, ey, CAM_W, ey, fill=WARN, width=2, tags="mark")
        self.lbl_cam.configure(text="第 %d 帧" % n, foreground=OK)
        self.update_marker_label()

    # ---------------- 刷新 ----------------
    def show_version(self):
        if not self.link or not self.link.version:
            return
        mods = {m.get("name"): m for m in self.link.version.get("module", [])}
        ota = mods.get("ota", {})
        prod = ota.get("product_name") or "Bambu Lab"
        fw = ota.get("sw_ver") or "?"
        self.title("Bambu Lab 看板 —— %s" % prod)
        extra = ", ".join("%s %s" % (m.get("name"), m.get("sw_ver"))
                          for m in self.link.version.get("module", []) if m.get("visible"))
        self.version_txt = "%s   固件 %s   %s" % (prod, fw, extra)
        self.lbl_ver.configure(text=self.version_txt)
        self.add_event("型号: %s, 固件 %s" % (prod, fw))

    def refresh(self):
        try:
            self._refresh()
        except tk.TclError as exc:
            log("!! refresh 界面错误: %s" % exc)
        except Exception:
            log_exc("refresh")

    def _refresh(self):
        if not self.link:
            return
        st = self.link.snapshot()
        if not st:
            return
        self.last_state = st
        self.emit_events(self.prev, st)
        self.prev = st

        gs = st.get("gcode_state", "UNKNOWN")
        cn = STATE_CN.get(gs, gs)
        color = {"RUNNING": ACC, "PAUSE": WARN, "FINISH": OK, "FAILED": BAD, "IDLE": DIM}.get(gs, FG)
        self.lbl_state.configure(text=cn, foreground=color)
        self.lbl_ctrl_state.configure(text="%s   %s" % (cn, st.get("subtask_name") or ""))
        ptype = st.get("print_type") or "?"
        if ptype == "cloud":
            self.lbl_ctrl_note.configure(
                text="为什么这些按钮按不动：打印机固件开了【授权校验】（新授权控制系统）。\n"
                     "带 print 的命令必须用拓竹 Studio 的密钥签名，没签名的会被拒 —— "
                     "你看到的「MQTT 命令校验失败」就是这么来的。\n"
                     "灯（system 类）不在校验范围，所以只有灯能按。\n"
                     "正规办法：在打印机上打开【开发者模式】（开了签名就可以不签），"
                     "或者直接用 Bambu Studio / 手机 App。")
        else:
            self.lbl_ctrl_note.configure(
                text="这盘是本地发的（print_type=%s）。注意：控制命令能不能用取决于"
                     "打印机的授权校验，跟本地/云端无关。" % ptype)
        task = st.get("subtask_name") or st.get("gcode_file") or ""
        if task != self.last_task:
            self.last_task = task
            self.layers = []
            self.layer_bbox = []
            self.layer_png_cache = {}
            self.last_layer_drawn = -1
            self.load_plate_info(task)
        self.lbl_task.configure(text=task[:36])
        # 阶段（打印机正在干嘛，例如 热床调平）
        self.lbl_stage.configure(text=("· " + stage_name(st.get("stg_cur")))
                                 if stage_name(st.get("stg_cur")) else "")
        # 正在打的是哪个文件 + 打到第几层
        gfile = st.get("gcode_file") or task or ""
        if gfile:
            self.lbl_file.configure(text="文件: %s" % gfile)
        else:
            self.lbl_file.configure(text="文件: —（现在没在打）")

        try:
            pct = int(st.get("mc_percent", 0))
        except (TypeError, ValueError):
            pct = 0
        self.pb.configure(value=pct)
        self.lbl_pct.configure(text="%d%%" % pct)
        left = st.get("mc_remaining_time", 0)
        self.lbl_left.configure(text="剩 %s   预计 %s" % (fmt_left(left), eta_text(left)))
        total = st.get("total_layer_num", 0)
        cur = st.get("layer_num", 0)
        self.lbl_layer.configure(text=("第 %s / %s 层" % (cur, total)) if total else "")

        lvl = st.get("spd_lvl")
        mag = st.get("spd_mag")
        self.lbl_speed.configure(text="%s%s" % (SPEED_CN.get(lvl, ""), ("  %s%%" % mag) if mag else ""))
        for l, b in self.speed_btns.items():
            b.state(["pressed"] if l == lvl else ["!pressed"])
        running = gs == "RUNNING"
        paused = gs == "PAUSE"
        # 云端发的盘, 局域网压根没有打印控制权 —— 那些按钮直接变灰, 别让人白按
        cloud = (st.get("print_type") or "") == "cloud"
        self.btn_pause.state(["!disabled"] if (running and not cloud) else ["disabled"])
        self.btn_resume.state(["!disabled"] if (paused and not cloud) else ["disabled"])
        self.btn_stop.state(["!disabled"] if ((running or paused) and not cloud) else ["disabled"])
        for b in self.speed_btns.values():
            b.state(["disabled"] if cloud else ["!disabled"])

        nz, nzt = st.get("nozzle_temper", 0), st.get("nozzle_target_temper", 0)
        bd, bdt = st.get("bed_temper", 0), st.get("bed_target_temper", 0)
        ch = st.get("chamber_temper", 0)
        self.lbl_nozzle.configure(text="%.1f" % nz)
        self.lbl_nozzle.sub.configure(text="目标 %.0f°C" % nzt)
        self.lbl_bed.configure(text="%.1f" % bd)
        self.lbl_bed.sub.configure(text="目标 %.0f°C" % bdt)
        self.lbl_cham.configure(text="%.1f" % ch)
        self.lbl_cham.sub.configure(text="°C")

        self.lbl_fan.configure(text="风扇: 模型 %s%%  辅助 %s%%  热端 %s%%" % (
            st.get("cooling_fan_speed", "?"), st.get("big_fan1_speed", "?"),
            st.get("heatbreak_fan_speed", "?")))
        self.lbl_wifi.configure(text="WiFi: %s" % st.get("wifi_signal", "?"))
        self.lbl_misc.configure(text="喷嘴 %smm %s   K值 %s   %s" % (
            st.get("nozzle_diameter", "?"), st.get("nozzle_type", "?"), st.get("k", "?"),
            "有卡" if st.get("sdcard") else "没卡"))

        trays = []
        ams = st.get("ams") or {}
        for unit in (ams.get("ams") or []):
            for tr in (unit.get("tray") or []):
                if tr.get("tray_type"):
                    trays.append((tr.get("tray_type"), tr.get("tray_color", "FFFFFFFF"), tr.get("remain")))
        vt = st.get("vt_tray") or {}
        if vt.get("tray_type"):
            trays.append((vt.get("tray_type"), vt.get("tray_color", "FFFFFFFF"), vt.get("remain")))
        if trays:
            t, c, r = trays[0]
            self.lbl_fil.configure(text="耗材: %s%s%s" % (
                t, ("  剩 %s%%" % r) if r else "",
                ("  (共 %d 卷)" % len(trays)) if len(trays) > 1 else "  外挂料盘"))
            self.swatch.itemconfigure(self.swatch_id, fill=color_of(c))
        else:
            self.lbl_fil.configure(text="耗材: 没检测到")
            self.swatch.itemconfigure(self.swatch_id, fill="#333c48")

        hms = st.get("hms") or []
        if hms:
            codes = ", ".join(str(h.get("code", "?")) for h in hms[:4])
            self.lbl_hms.configure(text="健康: 有 %d 条提示 —— %s" % (len(hms), codes),
                                   foreground=WARN)
        elif st.get("print_error"):
            self.lbl_hms.configure(text="健康: 报错码 %s" % st.get("print_error"), foreground=BAD)
        else:
            self.lbl_hms.configure(text="健康: 没有异常提示", foreground=DIM)

        ipcam = st.get("ipcam") or {}
        tl = ipcam.get("timelapse") == "enable"
        rc = ipcam.get("ipcam_record") == "enable"
        self.btn_tl.configure(text="延时摄影: " + ("开" if tl else "关"))
        self.btn_rec.configure(text="录像: " + ("开" if rc else "关"))
        self.draw_layer_map()
        self.fill_raw(st)

    def emit_events(self, old, new):
        """比一比新旧状态, 把变化写成事件。"""
        def ev(text):
            self.add_event(text)
        if not old:
            ev("收到第一份完整状态")
        gs_old, gs_new = old.get("gcode_state"), new.get("gcode_state")
        if gs_old != gs_new and gs_new:
            ev("状态: %s -> %s" % (STATE_CN.get(gs_old, gs_old or "?"), STATE_CN.get(gs_new, gs_new)))
            _name = new.get("subtask_name") or ""
            if not old:
                pass          # 刚启动时拿到的是"当前状态"，不是变化，别弹「打印完成」
            elif gs_new == "RUNNING":
                self.notify("开始打印了", _name or "(没拿到文件名)", "info")
            elif gs_new == "PAUSE":
                self.notify("打印暂停了", _name, "warn")
            elif gs_new == "FINISH":
                self.notify("打印完成", _name, "info")
            elif gs_new == "FAILED":
                self.notify("打印失败 / 报错了", _name, "bad")
            # 打完了（或失败）自动关灯 —— 灯是唯一实测能控制的
            if (gs_new in ("FINISH", "FAILED") and gs_old in ("RUNNING", "PAUSE")
                    and self.var_autolight.get()):
                try:
                    delay = int(float(self.var_lightdelay.get() or 0))
                except (TypeError, ValueError):
                    delay = 0
                delay = max(0, min(3600, delay))
                ev("打完了 → %s自动关灯" % (("%d 秒后" % delay) if delay else "马上"))
                self.after(delay * 1000, self.auto_light_off)
        t_old, t_new = old.get("subtask_name"), new.get("subtask_name")
        if t_new and t_old != t_new:
            ev("开始打印: %s" % t_new)
        p_old, p_new = old.get("mc_percent"), new.get("mc_percent")
        if p_new is not None and p_old != p_new:
            try:
                if int(p_new) // 5 != int(p_old or 0) // 5:
                    ev("进度 %s%%" % p_new)
            except (TypeError, ValueError):
                pass
        l_old, l_new = old.get("layer_num"), new.get("layer_num")
        if l_new is not None and l_old != l_new and l_new:
            ev("第 %s / %s 层" % (l_new, new.get("total_layer_num", "?")))
        for key, name in (("nozzle_target_temper", "喷嘴目标"), ("bed_target_temper", "热床目标")):
            if old.get(key) != new.get(key) and new.get(key) is not None:
                ev("%s温度改成 %.0f°C" % (name, new[key]))
        for key, name in (("nozzle_temper", "喷嘴"), ("bed_temper", "热床")):
            tgt = new.get(key.replace("_temper", "_target_temper"))
            if tgt and old.get(key) and new.get(key):
                was = abs(old[key] - tgt) <= 2
                now = abs(new[key] - tgt) <= 2
                if now and not was:
                    ev("%s到温 %.1f°C" % (name, new[key]))
        if (old.get("hms") or []) != (new.get("hms") or []):
            codes = [str(h.get("code")) for h in (new.get("hms") or [])]
            ev("健康提示变化: %s" % (codes or "没有提示了"))
        if old.get("print_error") != new.get("print_error"):
            ev("报错码: %s" % new.get("print_error"))
        if old.get("spd_lvl") != new.get("spd_lvl"):
            ev("速度档: %s" % SPEED_CN.get(new.get("spd_lvl"), new.get("spd_lvl")))
        if (old.get("s_obj") or []) != (new.get("s_obj") or []):
            ev("已跳过的零件: %s" % (new.get("s_obj") or "无"))
        for key, name in (("tray_type", "耗材"), ("tray_color", "耗材颜色")):
            vo = (old.get("vt_tray") or {}).get(key)
            vn = (new.get("vt_tray") or {}).get(key)
            if vo != vn and vn:
                ev("%s: %s -> %s" % (name, vo or "无", vn))
        for node in (new.get("lights_report") or []):
            for o in (old.get("lights_report") or []):
                if o.get("node") == node.get("node") and o.get("mode") != node.get("mode"):
                    ev("灯 %s: %s" % (node.get("node"), node.get("mode")))

    def load_plate_info(self, task):
        """一次把 3mf 拉下来，同时得到：这一盘的耗材/时间 + 每一层的盘面图。"""
        self.lbl_weight.configure(text="")
        if not task or not self.files:
            return          # 空闲时没有文件，别去 FTP 找一个空名字（会报 550）
        name = task if task.lower().endswith(".3mf") else task + ".3mf"

        def work():
            try:
                data = self.files.read_bytes("/cache", name)
            except Exception as exc:
                log("读盘信息失败: %s: %s" % (type(exc).__name__, exc))
                self.q.put(("msg", "这盘的 3mf 不在打印机 /cache 里，耗材和层图都算不了"))
                return
            # ① 耗材 / 预测时间
            try:
                zf = zipfile.ZipFile(io.BytesIO(data))
                target = next((n for n in zf.namelist()
                               if n.lower().endswith("slice_info.config")), None)
                if target:
                    root = ET.fromstring(zf.read(target))
                    for plate in root.iter("plate"):
                        md = {m.get("key"): m.get("value") for m in plate.findall("metadata")}
                        w = md.get("weight")
                        pred = md.get("prediction")
                        txt = "这一盘: 预计用 %s 克耗材" % w if w else ""
                        if pred:
                            try:
                                txt += "，切片预测 %d 分 %d 秒" % (int(pred) // 60, int(pred) % 60)
                            except ValueError:
                                pass
                        self.q.put(("msg", txt))
                        self.q.put(("event", "读到盘信息: " + txt))
                        break
            except Exception:
                log_exc("slice_info")
            # ② 每层的盘面图（纯算，不用标定）
            try:
                zf = zipfile.ZipFile(io.BytesIO(data))
                gname = next((n for n in zf.namelist() if n.lower().endswith(".gcode")), None)
                if not gname:
                    self.q.put(("msg", "这个 3mf 里没有 gcode，层图算不了"))
                    return
                text = zf.read(gname).decode("utf-8", "replace")
                layers, bboxes, lh, initial = parse_layers(text)
                self.q.put(("layers", (layers, bboxes, lh, initial)))
            except Exception:
                log_exc("parse_layers")

        threading.Thread(target=work, daemon=True).start()

    def cur_layer_n(self):
        try:
            return int(self.last_state.get("layer_num") or 0)
        except (TypeError, ValueError):
            return 0

    def layer_info_text(self, cur=None):
        cur = self.cur_layer_n() if cur is None else cur
        if not (1 <= cur <= len(self.layer_bbox)):
            return ""
        b = self.layer_bbox[cur - 1]
        z = self.layer_z0 + (cur - 1) * self.layer_zh
        if not b:
            return "第 %d 层：这层没有挤出移动" % cur
        return ("第 %d 层  Z ≈ %.2f mm　X %.0f~%.0f（%.0fmm）　Y %.0f~%.0f（%.0fmm）"
                % (cur, z, b[0], b[2], b[2] - b[0], b[1], b[3], b[3] - b[1]))

    # ---- 标记 / 标定 ----
    def set_marker_src(self):
        """切换标记来源。"""
        cam = self.marker_src.get().startswith("摄像头")
        self.marker_dot = None
        if not cam:
            self.marker_worker_on = False
        if self.layer_canvas is not None:
            self.layer_canvas.delete("all")
            self.last_layer_drawn = -1
            self.draw_layer_map()
        if cam:
            self.start_marker_worker()
            if not self.cam:
                self.add_event("标记来源切到摄像头，但摄像头没开（看点板上「开摄像头」）")
        else:
            self.marker_px = None
        self.update_marker_label()

    def start_marker_worker(self):
        if self.marker_worker_on:
            return
        self.marker_worker_on = True

        def work():
            # 只要摄像头开着就一直识别（不管红点用哪个档驱动）——
            # 这样识别画面上永远有红线/黄框可看
            while self.marker_worker_on and self.cam is not None:
                jpeg = self.cam.grab_jpeg()
                if jpeg:
                    blobs = find_marker_blobs(jpeg)
                    self.marker_blobs = blobs
                    b = pick_blue_blob(blobs, self.marker_target)
                    if b:
                        self.marker_px = (b["x"], b["y"])
                        self.marker_target = (b["x"], b["y"])
                        self.marker_nblobs = len(blobs)
                    ey = plate_front_edge_y(jpeg)
                    if ey:
                        self.plate_edge_y = ey
                    if time.time() - self.last_recog_save > RECOG_EVERY:
                        self.last_recog_save = time.time()
                        p = self.save_recog_shot(jpeg)
                        if p:
                            self.q.put(("msg", "识别图已存: " + p))
                time.sleep(1.5)
            self.marker_worker_on = False

        threading.Thread(target=work, daemon=True).start()

    def on_cam_click(self, evt):
        """在看板那张摄像头画面上点一下 -> 锁定那块蓝色标，之后跟着它走。"""
        jpeg = self.cam.grab_jpeg() if self.cam else None
        blobs = find_marker_blobs(jpeg)
        if not blobs:
            messagebox.showinfo("没找到蓝块", "这一帧里没找到蓝色标。\n"
                                              "确认蓝标在画面里、而且光线够。")
            return
        # 画布坐标 -> 全分辨率坐标
        fx = evt.x * 1536.0 / CAM_W
        fy = evt.y * 1080.0 / CAM_H
        b = pick_blue_blob(blobs, (fx, fy), max_jump=1e9)
        self.marker_target = (b["x"], b["y"])
        self.marker_px = (b["x"], b["y"])
        self.marker_src.set("摄像头·蓝标")
        self.set_marker_src()
        self.add_event("锁定蓝标: 像素 (%.0f, %.0f)，画面里一共 %d 个蓝块"
                       % (b["x"], b["y"], len(blobs)))

    def marker_mm(self):
        """标记现在在盘上的位置（毫米）。假标记会自己动；摄像头要走标定。"""
        if self.marker_src.get().startswith("假"):
            b = None
            cur = self.cur_layer_n()
            if 1 <= cur <= len(self.layer_bbox):
                b = self.layer_bbox[cur - 1]
            if not b:
                b = (60.0, 90.0, 200.0, 170.0)
            cx = (b[0] + b[2]) / 2.0
            cy = (b[1] + b[3]) / 2.0
            rx = max(5.0, (b[2] - b[0]) / 2.0) * 0.85
            ry = max(5.0, (b[3] - b[1]) / 2.0) * 0.85
            t = time.time()
            return (cx + rx * math.cos(t * 0.9), cy + ry * math.sin(t * 1.3))
        if not self.marker_px:
            return None
        # 第一优先：老大教的「分工法」—— X 看喷头蓝标、Y 看盘子前沿
        # （A1 是床动式：前后轴动的是底盘，喷头前后不动，所以 Y 只能看盘子）
        if self.cal_x and self.cal_y:
            x0, x1 = self.cal_x
            y0, y1 = self.cal_y
            if None not in (x0, x1, y0, y1, self.plate_edge_y) and x1 != x0 and y1 != y0:
                xm = (self.marker_px[0] - x0) / float(x1 - x0) * 256.0
                ym = (self.plate_edge_y - y0) / float(y1 - y0) * 256.0
                return (xm, ym)
        # 第二优先：本地校准（盘面 4 角）+ 可选的修正
        base = None
        if self.local_H_inv:
            r = apply_homography(self.local_H_inv, self.marker_px[0], self.marker_px[1])
            if r:
                base = (r[0] * 256.0, r[1] * 256.0)
        if base is None:
            base = (self.marker_px[0], self.marker_px[1])
        if self.affine:
            return apply_affine(self.affine, base[0], base[1])
        return base if self.local_H_inv else None

    def marker_base_mm(self):
        """只走本地校准那一步（给记标定点用）。"""
        if not self.marker_px:
            return None
        if self.local_H_inv:
            r = apply_homography(self.local_H_inv, self.marker_px[0], self.marker_px[1])
            if r:
                return (r[0] * 256.0, r[1] * 256.0)
        return (self.marker_px[0], self.marker_px[1])

    def update_marker_label(self):
        # 识别结果统一由 marker_status_text() 生成：电脑上的标签、下面那行、
        # 还有网页黑条，都用同一份判断，避免"界面上说的"和"实际算的"不一致
        txt = self.marker_status_text()
        for w in (self.lbl_marker, getattr(self, "lbl_cam_status", None)):
            if w is None:
                continue
            try:
                w.configure(text=txt)
            except tk.TclError:
                pass
        return

    def _update_marker_label_old(self):
        if self.marker_src.get().startswith("假"):
            mm = self.marker_mm()
            self.lbl_marker.configure(
                text=("假标记（演示）：盘上 (%.0f, %.0f) mm　—— 这个红点是编出来的，"
                      "只用来先看链路通不通" % mm) if mm else "假标记：等层图算好")
            return
        if self.marker_px is None:
            self.lbl_marker.configure(
                text="摄像头：还没找到蓝标 —— 画面里要能看见喷头上那块蓝标，"
                     "而且要先把看板的摄像头打开")
            return
        if self.cal_x and self.cal_y:
            mm = self.marker_mm()
            self.lbl_marker.configure(
                text=("摄像头：盘上 (%.0f, %.0f) mm　（X 看喷头标、Y 看盘子前沿）" % (mm[0], mm[1]))
                if mm else "摄像头：四步标定齐了，但换算不出来（盘子前沿没抓到？）")
            return
        if self.affine:
            mm = self.marker_mm()
            self.lbl_marker.configure(
                text="摄像头：像素 (%.0f, %.0f) → 盘上 (%.1f, %.1f) mm　"
                     "（本地校准 + %d 点修正）"
                     % (self.marker_px[0], self.marker_px[1], mm[0], mm[1], len(self.calib)))
        elif self.local_H_inv:
            mm = self.marker_mm()
            self.lbl_marker.configure(
                text="摄像头：像素 (%.0f, %.0f) → 盘上 (%.1f, %.1f) mm　（本地校准：盘的 4 个角）"
                     "　⚠️ 这是**标签**的位置，不是喷嘴 —— 喷嘴在它下方有个固定偏移，"
                     "记 3 个标定点就能修掉"
                     % (self.marker_px[0], self.marker_px[1], mm[0], mm[1]) if mm
                     else "摄像头：本地校准好了，但换算失败")
        else:
            self.lbl_marker.configure(
                text="摄像头：在像素 (%.0f, %.0f) 找到蓝标　还没标定 —— "
                     "点「本地校准（点盘的4个角）」最快：在画面上点盘子的四个角就行，不用动打印机"
                     % self.marker_px)

    def record_calib(self):
        if self.marker_px is None:
            messagebox.showinfo("还没有标记位置",
                                "先切到「摄像头·蓝标」，等画面里出现红十字（说明找到蓝标了）再记点。")
            return
        base = self.marker_base_mm()
        x = simpledialog.askfloat("标定点", "喷嘴现在的 X 是多少 mm？", parent=self)
        if x is None:
            return
        y = simpledialog.askfloat("标定点", "喷嘴现在的 Y 是多少 mm？", parent=self)
        if y is None:
            return
        # 存的是"本地校准算出来的位置 -> 真实位置"，这样两层能叠起来
        self.calib.append((tuple(base), (float(x), float(y))))
        if len(self.calib) >= 3:
            params, err = fit_affine(self.calib)
            self.affine = params
            log("修正标定: %d 个点, params=%s, 残差=%.2f mm"
                % (len(self.calib), params, err if err is not None else -1))
            self.add_event("修正标定完成（%d 点），最大残差 %.2f mm" % (len(self.calib), err or 0))
        self.update_marker_label()

    def show_quad(self):
        """把你点的 4 个角画在画面上，自己看一眼点对没有。"""
        q = self.cfg.get("local_quad")
        if not q or len(q) != 4:
            messagebox.showinfo("还没标定", "先在「本地校准」里点盘子的 4 个角。")
            return
        if not self.cam:
            messagebox.showinfo("先开摄像头", "先在「看板」页点「开摄像头」。")
            return
        jpeg = self.cam.grab_jpeg()
        if not jpeg:
            messagebox.showinfo("还没画面", "摄像头还没出画面，等一下再试。")
            return
        try:
            im = Image.open(io.BytesIO(jpeg)).convert("RGB")
        except Exception:
            log_exc("show_quad")
            return
        d = ImageDraw.Draw(im)
        pts = [tuple(p) for p in q]
        d.polygon(pts, outline=(255, 60, 60), width=6)
        names = ["1 left-front (0,0)", "2 right-front (256,0)",
                 "3 right-back (256,256)", "4 left-back (0,256)"]
        for i, (x, y) in enumerate(pts):
            d.ellipse((x - 16, y - 16, x + 16, y + 16), fill=(255, 60, 60))
            d.text((x + 22, y - 34), names[i], fill=(255, 220, 60))
        if self.marker_px:
            mx, my = self.marker_px
            d.ellipse((mx - 22, my - 22, mx + 22, my + 22), outline=(60, 220, 255), width=6)
        im = im.resize((CAL_W, CAL_H), Image.LANCZOS)
        win = tk.Toplevel(self)
        win.title("你点的 4 个角 + 现在锁定的蓝标（青圈）")
        win.configure(bg=BG)
        self.quad_photo = ImageTk.PhotoImage(im)
        c = tk.Canvas(win, width=CAL_W, height=CAL_H, bg="#0a0d11", highlightthickness=0)
        c.pack(padx=12, pady=12)
        c.create_image(0, 0, anchor="nw", image=self.quad_photo)

    def flip_quad(self, which):
        """把标定的前后 / 左右对调一下（点反了不用重新点）。"""
        q = self.cfg.get("local_quad")
        if not q or len(q) != 4:
            messagebox.showinfo("还没标定", "先点完 4 个角。")
            return
        q = [list(p) for p in q]
        if which == "y":
            q = [q[3], q[2], q[1], q[0]]
        else:
            q = [q[1], q[0], q[3], q[2]]
        H = homography_from_quad([tuple(p) for p in q])
        if H is None:
            return
        self.local_H_inv = invert3(H)
        self.local_quad = [tuple(p) for p in q]
        self.cfg["local_quad"] = q
        save_cfg(self.cfg)
        self.add_event("本地校准：" + ("前后对调" if which == "y" else "左右对调"))
        self.update_marker_label()

    def record_corner(self, name, x_mm, y_mm):
        """记一个**角**：喷嘴现在就在盘子的这个角上（x_mm/y_mm 是这个角的坐标）。

        X 只看喷头上那块标（A1 床动头不动，标只反映 X）；
        Y 只看盘子前沿在画面里的位置（前后动的是盘子，不是喷头）。
        四个角里任意两个「左/右」就能定 X，任意两个「前/后」就能定 Y。
        """
        if not self.marker_px:
            messagebox.showinfo("还没有标记", "先切到「摄像头·蓝标」那一档，"
                                             "等黄框套在喷头那块红标上再记。")
            return
        if not self.plate_edge_y:
            messagebox.showinfo("没找到盘子前沿", "画面里现在找不到盘子的前沿，"
                                                 "等摄像头刷新一下再试。")
            return
        cx = list(self.cal_x) if self.cal_x else [None, None]
        cx[0 if x_mm == 0 else 1] = self.marker_px[0]
        self.cal_x = tuple(cx)
        cy = list(self.cal_y) if self.cal_y else [None, None]
        cy[0 if y_mm == 0 else 1] = self.plate_edge_y
        self.cal_y = tuple(cy)
        self.add_event("标定 %s(%d,%d)　← 贴纸 x=%.0f　盘子前沿 y=%.0f"
                       % (name, x_mm, y_mm, self.marker_px[0], self.plate_edge_y))
        self.cfg["cal_x"] = list(self.cal_x) if self.cal_x else []
        self.cfg["cal_y"] = list(self.cal_y) if self.cal_y else []
        save_cfg(self.cfg)
        self.update_marker_label()

    def reset_calib(self):
        self.calib = []
        self.affine = None
        self.local_H_inv = None
        self.local_quad = None
        self.cal_x = None
        self.cal_y = None
        for k in ("local_quad", "cal_x", "cal_y"):
            self.cfg.pop(k, None)
        save_cfg(self.cfg)
        self.add_event("标定已清空（本地校准 + 四步标定）")
        self.notify("标定丢掉了", "红点回到「纯估算」状态，要重新记四个角", "warn")
        self.update_marker_label()

    # ---- 本地校准：点盘子的 4 个角 ----
    def open_calib_window(self):
        if not self.cam:
            messagebox.showinfo("先开摄像头", "先在「看板」页点「开摄像头」，再来标定。")
            return
        jpeg = self.cam.grab_jpeg()
        if not jpeg:
            messagebox.showinfo("还没画面", "摄像头还没出画面，等一下再试。")
            return
        try:
            im = Image.open(io.BytesIO(jpeg)).convert("RGB").resize((CAL_W, CAL_H), Image.LANCZOS)
        except Exception:
            log_exc("calib open")
            return
        if self.calib_win is not None and self.calib_win.winfo_exists():
            self.calib_win.destroy()
        win = tk.Toplevel(self)
        self.calib_win = win
        win.title("本地校准 —— 点盘子的 4 个角")
        win.configure(bg=BG)
        self.calib_photo = ImageTk.PhotoImage(im)
        c = tk.Canvas(win, width=CAL_W, height=CAL_H, bg="#0a0d11", highlightthickness=0)
        c.pack(padx=12, pady=(10, 4))
        c.create_image(0, 0, anchor="nw", image=self.calib_photo)
        self.calib_canvas = c
        self.calib_clicks = []
        ttk.Label(win, text="按顺序点盘子的 4 个角：① 左前(0,0)　② 右前(256,0)　"
                            "③ 右后(256,256)　④ 左后(0,256)",
                  foreground=WARN).pack(anchor="w", padx=14)
        ttk.Label(win, text="⚠️ 「前」= 画面【下方】那条边（靠近你的一侧，打印头/龙门在画面上方是后面）；"
                            "「左」= 画面左边。点反了就用「前后对调 / 左右对调」",
                  foreground=WARN, wraplength=900).pack(anchor="w", padx=14, pady=(2, 0))
        ttk.Label(win, text="这张照片是打开窗口那一刻冻结的（相机不动，所以没关系）。"
                            "点错就点「重来」。",
                  foreground=DIM).pack(anchor="w", padx=14, pady=(2, 6))
        row = ttk.Frame(win)
        row.pack(anchor="w", padx=14, pady=(0, 12))
        ttk.Button(row, text="重来", command=self.open_calib_window).pack(side="left")
        self.lbl_calib = ttk.Label(row, text="还没开始点", foreground=FG)
        self.lbl_calib.pack(side="left", padx=12)
        c.bind("<Button-1>", self.calib_click)

    def calib_click(self, evt):
        if len(self.calib_clicks) >= 4 or self.calib_canvas is None:
            return
        fx = evt.x * CAM_FULL_W / float(CAL_W)
        fy = evt.y * CAM_FULL_H / float(CAL_H)
        self.calib_clicks.append((fx, fy))
        c = self.calib_canvas
        n = len(self.calib_clicks)
        c.create_oval(evt.x - 10, evt.y - 10, evt.x + 10, evt.y + 10, outline=BAD, width=3)
        c.create_text(evt.x + 18, evt.y - 16, text=str(n), fill=BAD, font=(MONO, 14, "bold"))
        self.lbl_calib.configure(text="已点 %d / 4" % n)
        if n == 4:
            self.finish_calib()

    def finish_calib(self):
        quad = list(self.calib_clicks)
        H = homography_from_quad(quad)          # 盘单位坐标 -> 像素
        if H is None:
            self.lbl_calib.configure(text="这 4 个点算不出来（可能有三个点几乎在一条线上），点「重来」")
            return
        inv = invert3(H)                        # 像素 -> 盘单位坐标
        if inv is None:
            self.lbl_calib.configure(text="矩阵不可逆，点「重来」")
            return
        self.local_H_inv = inv
        self.local_quad = quad
        self.cfg["local_quad"] = [list(p) for p in quad]
        save_cfg(self.cfg)
        back = []
        for (fx, fy) in quad:
            r = apply_homography(inv, fx, fy)
            back.append("(%.0f,%.0f)" % (r[0] * 256.0, r[1] * 256.0) if r else "?")
        self.lbl_calib.configure(
            text="标定完成！4 个角反算回来: %s　（应该正好是 0 / 256；不对就是点歪了）"
                 % " ".join(back))
        self.add_event("本地校准完成：点了盘子的 4 个角（画面 ↔ 盘坐标）")
        # 校准完自动切到摄像头，不然红点还是假的（这个坑踩过）
        self.marker_src.set("摄像头·蓝标")
        self.set_marker_src()
        c = self.calib_canvas
        pts = []
        for fx, fy in quad:
            pts += [fx * CAL_W / CAM_FULL_W, fy * CAL_H / CAM_FULL_H]
        c.create_polygon(pts, outline=COOL, width=3, fill="")
        self.update_marker_label()

    def update_marker(self):
        try:
            mm = self.marker_mm()
            c = self.layer_canvas
            if c is not None:
                if mm:
                    size = LAYER_PX
                    # 换算离谱的时候（贴纸比喷嘴高，单应会算出盘外的值）把点钉在画布边上，
                    # 不然它被画到画布外面，看起来就像「点没了」
                    x = min(max(mm[0] / 256.0 * size, 8), size - 8)
                    y = min(max(size - mm[1] / 256.0 * size, 8), size - 8)
                    if self.marker_dot is None:
                        self.marker_dot = c.create_oval(x - 8, y - 8, x + 8, y + 8,
                                                        outline=BAD, width=3)
                    else:
                        c.coords(self.marker_dot, x - 8, y - 8, x + 8, y + 8)
                        c.tag_raise(self.marker_dot)
                elif self.marker_dot is not None:
                    c.delete(self.marker_dot)
                    self.marker_dot = None
            self.update_marker_label()
        except tk.TclError:
            pass
        self.after(150, self.update_marker)

    def draw_layer_map(self):
        c = self.layer_canvas
        if c is None:
            return
        cur = self.cur_layer_n()
        if cur == self.last_layer_drawn and self.layers:
            return
        self.last_layer_drawn = cur
        size = LAYER_PX
        sc = size / float(GRID)
        c.delete("all")
        self.marker_dot = None   # 画布清空了，旧红点 id 作废，得让 update_marker 重建
        self.marker_dot = None
        c.create_rectangle(0, 0, size - 1, size - 1, outline="#46545f")
        # 每 32mm 一条参考线 + 刻度
        for mm in range(0, 257, 32):
            p = mm / 256.0 * size
            c.create_line(p, 0, p, size, fill="#28313a")
            c.create_line(0, size - p, size, size - p, fill="#28313a")
            c.create_text(p + 4, size - 12, text=str(mm), fill="#6b7a89",
                          font=(MONO, 8), anchor="w")
            c.create_text(26, size - p - 4, text=str(mm), fill="#6b7a89",
                          font=(MONO, 8), anchor="sw")
        if not self.layers:
            c.create_text(size // 2, size // 2,
                          text="层图还没准备好\n（这一盘的 3mf 要在打印机的 /cache 里）",
                          fill=DIM, font=(FONT, 11), justify="center")
            self.lbl_layer_big.configure(text="等开始打印后会自动算出来")
            return
        g = self.layers[cur - 1]
        # 按行把连续格子合并成一个矩形再画（几千格 -> 几百个矩形，快很多）
        for cy in range(GRID):
            base = cy * GRID
            y0 = (GRID - 1 - cy) * sc
            run = None
            for cx in range(GRID + 1):
                on = (cx < GRID) and g[base + cx]
                if on and run is None:
                    run = cx
                elif not on and run is not None:
                    c.create_rectangle(run * sc, y0, cx * sc, y0 + sc, fill=COOL, outline="")
                    run = None
        b = self.layer_bbox[cur - 1]
        if b:
            c.create_rectangle(b[0] / 256.0 * size, size - b[3] / 256.0 * size,
                               b[2] / 256.0 * size, size - b[1] / 256.0 * size,
                               outline=WARN, width=2)
        self.lbl_layer_big.configure(text=self.layer_info_text(cur))

    def layer_image(self, idx, size=300):
        """把某一层画成一张图（浏览器要）。带缓存。"""
        key = (idx, size)
        if key in self.layer_png_cache:
            return self.layer_png_cache[key]
        if not (1 <= idx <= len(self.layers)):
            return None
        sc = size / float(GRID)
        im = Image.new("RGB", (size, size), (18, 22, 28))
        d = ImageDraw.Draw(im)
        d.rectangle((0, 0, size - 1, size - 1), outline=(70, 84, 98))
        g = self.layers[idx - 1]
        for cy in range(GRID):
            base = cy * GRID
            y0 = (GRID - 1 - cy) * sc
            for cx in range(GRID):
                if g[base + cx]:
                    x0 = cx * sc
                    d.rectangle((x0, y0, x0 + sc - 1, y0 + sc - 1), fill=(90, 220, 200))
        b = self.layer_bbox[idx - 1]
        if b:
            d.rectangle((b[0] / 256.0 * size, size - b[3] / 256.0 * size,
                         b[2] / 256.0 * size, size - b[1] / 256.0 * size),
                        outline=(255, 170, 0))
        if ImageDraw is not None:
            d.text((6, 6), "layer %d" % idx, fill=(230, 236, 242))
        self.layer_png_cache[key] = im
        if len(self.layer_png_cache) > 400:
            self.layer_png_cache.clear()
            self.layer_png_cache[key] = im
        return im

    def web_layer_png(self, idx):
        im = self.layer_image(idx, 300)
        if im is None:
            return None
        buf = io.BytesIO()
        im.save(buf, "PNG")
        return buf.getvalue()

    def fill_raw(self, st):
        if self.nb.tab(self.nb.select(), "text") != "全部字段":
            return
        now = time.time()
        if now - self.last_raw_fill < 2.0:
            return
        self.last_raw_fill = now
        self.tree_raw.delete(*self.tree_raw.get_children())
        for k, v in sorted(st.items(), key=lambda kv: kv[0]):
            s = json.dumps(v, ensure_ascii=False)
            self.tree_raw.insert("", "end", values=(k, s[:400]))

    # ---------------- 计时 / 曲线 ----------------
    def tick(self):
        try:
            st = self.last_state
            if st:
                now = time.time()
                if now - self.last_poll >= SAMPLE_SEC:
                    self.last_poll = now
                    nz = st.get("nozzle_temper", 0)
                    bd = st.get("bed_temper", 0)
                    nzt = st.get("nozzle_target_temper", 0)
                    bdt = st.get("bed_target_temper", 0)
                    self.samples.append((now, nz, bd, nzt, bdt))
                    if len(self.samples) > CHART_POINTS:
                        self.samples = self.samples[-CHART_POINTS:]
                    self.cool.add(now, nz, bd, nzt, bdt)
                    self.draw_chart()
                    self.update_cool(st)
            self.after(1000, self.tick)
        except Exception:
            log_exc("tick")
            self.after(2000, self.tick)

    def draw_chart(self):
        c = self.chart
        c.delete("all")
        w = c.winfo_width() or CHART_W
        h = c.winfo_height() or CHART_H
        pad = 22
        c.create_line(pad, h - pad, w - 4, h - pad, fill="#39434f")
        c.create_line(pad, 4, pad, h - pad, fill="#39434f")
        if len(self.samples) < 2:
            c.create_text(pad + 8, 16, anchor="w", text="在采数据…", fill=DIM, font=(FONT, 9))
            return
        vals = []
        for s in self.samples:
            vals += [s[1], s[2], s[3], s[4]]
        top = max(60.0, max(vals) + 10)
        c.create_text(4, 6, anchor="nw", text="%.0f°C" % top, fill=DIM, font=(MONO, 8))
        c.create_text(4, h - pad - 10, anchor="nw", text="0°C", fill=DIM, font=(MONO, 8))
        n = len(self.samples)
        step = (w - pad - 8) / max(1, n - 1)

        def poly(idx, col, width=2, smooth=True, dash=False):
            pts = []
            for i, s in enumerate(self.samples):
                y = (h - pad) - (float(s[idx]) / top) * (h - pad - 8)
                pts += [pad + i * step, y]
            if len(pts) >= 4:
                kw = {"dash": (6, 4)} if dash else {}
                c.create_line(*pts, fill=col, width=width, smooth=smooth, **kw)

        # 先画目标温度（虚线），再画实际温度（实线）盖在上面
        poly(3, TGT_HOT, width=1, smooth=False, dash=True)
        poly(4, TGT_COOL, width=1, smooth=False, dash=True)
        poly(1, HOT)
        poly(2, COOL)
        c.create_text(w - 6, 6, anchor="ne", text="喷嘴", fill=HOT, font=(FONT, 9))
        c.create_text(w - 6, 20, anchor="ne", text="热床", fill=COOL, font=(FONT, 9))
        c.create_text(w - 52, 6, anchor="ne", text="目标", fill=TGT_HOT, font=(FONT, 9))
        c.create_text(w - 52, 20, anchor="ne", text="目标", fill=TGT_COOL, font=(FONT, 9))

    def update_cool(self, st):
        """算「还要多久凉下来」——用拟合出来的时间常数，没测到就用粗估。"""
        env = COOL_ENV
        bits = []
        for key, name, temp, tgt, goal in (
                ("nozzle", "喷嘴", st.get("nozzle_temper", 0),
                 st.get("nozzle_target_temper", 0), COOL_GOAL["nozzle"]),
                ("bed", "热床", st.get("bed_temper", 0),
                 st.get("bed_target_temper", 0), COOL_GOAL["bed"])):
            try:
                temp = float(temp)
                tgt = float(tgt)
            except (TypeError, ValueError):
                continue
            tau = self.cool.get_tau(key)
            src = self.cool.source(key)
            if temp <= goal:
                bits.append("%s 已经 %.1f°C，能碰了" % (name, temp))
                continue
            secs = cool_estimate(tau, temp, goal, env)
            if secs is None:
                bits.append("%s 现在 %.1f°C" % (name, temp))
                continue
            if tgt > goal + 2:
                bits.append("%s 现在就停的话，约 %s 凉到 %.0f°C（%s）"
                            % (name, fmt_min(secs), goal, src))
            else:
                bits.append("%s 还要约 %s 凉到 %.0f°C（%s）" % (name, fmt_min(secs), goal, src))
        hint = "" if len(self.cool.tau) >= 2 else \
            "　（还没测到你这里的降温过程，先用粗估常数；这盘打完后凉一次就换成实测）"
        txt = "冷却估计　" + "　|　".join(bits) + hint
        self.cool_text = txt
        self.lbl_cool.configure(text=txt)

    # ---------------- 打印历史 ----------------
    def load_history(self):
        if not self.files:
            messagebox.showinfo("先连打印机", "先点「连接」。")
            return
        self.lbl_hist.configure(text="正在读…")

        def work():
            try:
                files = self.files.list_dir("/timelapse")
                vids = [x for x in files if x[0].lower().endswith(".avi")]
                vids.sort(key=lambda x: x[0])
                self.q.put(("hist", vids))
            except Exception as exc:
                log_exc("load_history")
                self.q.put(("hist", []))

        threading.Thread(target=work, daemon=True).start()

    def fill_history(self, vids):
        self.tree_hist.delete(*self.tree_hist.get_children())
        self.history = vids
        for name, size, when, isdir in reversed(vids):
            m = re.match(r"video_(\d{4})-(\d{2})-(\d{2})_(\d{2})-(\d{2})-(\d{2})", name)
            stamp = "%s-%s-%s %s:%s:%s" % m.groups() if m else when
            self.tree_hist.insert("", "end", values=(stamp, fmt_size(size), name))
        total = sum(v[1] for v in vids)
        self.lbl_hist.configure(text="共 %d 段延时摄影, 合计 %s" % (len(vids), fmt_size(total)))
        self.add_event("读到 %d 段延时摄影（%s）" % (len(vids), fmt_size(total)))

    def on_hist_select(self, _e=None):
        sel = self.tree_hist.selection()
        if not sel:
            return
        name = self.tree_hist.item(sel[0], "values")[2]
        self.sel_history = name
        thumb = name[:-4] + ".jpg"
        if thumb in self.thumb_cache:
            self.show_hist_thumb(thumb, self.thumb_cache[thumb])
            return
        self.canvas_hist.delete("all")
        self.canvas_hist.create_text(THUMB_W // 2, THUMB_H // 2, text="正在取封面…", fill=DIM,
                                     font=(FONT, 10))
        info = "文件: %s\n大小: %s\n" % (name, fmt_size(dict(
            (v[0], v[1]) for v in self.history).get(name, 0)))
        self.hist_text.configure(state="normal")
        self.hist_text.delete("1.0", "end")
        self.hist_text.insert("end", info)
        self.hist_text.configure(state="disabled")

        def work():
            try:
                data = self.files.read_bytes("/timelapse/thumbnail", thumb)
                im = Image.open(io.BytesIO(data)).convert("RGB").resize((THUMB_W, THUMB_H),
                                                                        Image.LANCZOS)
                self.q.put(("thumb", (thumb, im)))
            except Exception as exc:
                log("取封面失败 %s: %s" % (thumb, exc))
                self.q.put(("thumb", (thumb, None)))

        threading.Thread(target=work, daemon=True).start()

    def show_hist_thumb(self, thumb, im):
        if im is not None:
            self.thumb_cache[thumb] = im
        if im is None:
            self.canvas_hist.delete("all")
            self.canvas_hist.create_text(THUMB_W // 2, THUMB_H // 2, text="这盘没有封面图",
                                         fill=DIM, font=(FONT, 10))
            return
        try:
            self.thumb_photo = ImageTk.PhotoImage(im)
        except Exception:
            log_exc("thumb")
            return
        self.canvas_hist.delete("all")
        self.canvas_hist.create_image(0, 0, anchor="nw", image=self.thumb_photo)

    def _dl(self, remote_dir, sub, names):
        os.makedirs(os.path.join(DL_ROOT, sub), exist_ok=True)
        for name in names:
            try:
                local = os.path.join(DL_ROOT, sub, name)

                def prog(done, total, n=name):
                    self.q.put(("msg", "正在下载 %s: %s / %s"
                                % (n, fmt_size(done), fmt_size(total) if total else "?")))

                size = self.files.download(remote_dir, name, local, progress=prog)
                self.q.put(("dl", "下好了 %s (%s)" % (name, fmt_size(size))))
            except Exception as exc:
                log_exc("download " + name)
                self.q.put(("dl", "下载失败 %s: %s" % (name, exc)))

    def dl_selected_video(self):
        if not self.sel_history:
            messagebox.showinfo("先选一段", "在上面的列表里点一段。")
            return
        name = self.sel_history
        self.set_status("正在下载 " + name)
        threading.Thread(target=self._dl, args=("/timelapse", "延时摄影", [name]),
                         daemon=True).start()

    def dl_all_videos(self):
        if not self.history:
            return
        names = [v[0] for v in self.history]
        if not messagebox.askyesno("下载全部", "要下 %d 段视频，合计 %s，继续吗？"
                                   % (len(names), fmt_size(sum(v[1] for v in self.history)))):
            return
        self.set_status("正在下载 %d 段视频…" % len(names))
        threading.Thread(target=self._dl, args=("/timelapse", "延时摄影", names),
                         daemon=True).start()

    def open_dl_folder(self):
        os.makedirs(DL_ROOT, exist_ok=True)
        os.startfile(DL_ROOT)

    # ---------------- 存储 ----------------
    def load_disk(self):
        if not self.files:
            messagebox.showinfo("先连打印机", "先点「连接」。")
            return
        self.lbl_disk.configure(text="正在统计…（十几秒）")

        def work():
            rows = []
            for path, name, desc in REMOTE_DIRS:
                try:
                    total, n = self.files.dir_size(path)
                    rows.append((path, name, desc, n, total))
                except Exception as exc:
                    log("统计 %s 失败: %s" % (path, exc))
                    rows.append((path, name, desc, -1, 0))
            self.q.put(("disk", rows))

        threading.Thread(target=work, daemon=True).start()

    def fill_disk(self, rows):
        self.show_disk_rows()
        total = 0
        for path, name, desc, n, size in rows:
            item = self.dir_rows.get(path)
            if not item:
                continue
            v = list(self.tree_disk.item(item, "values"))
            v[2] = str(n) if n >= 0 else "读不到"
            v[3] = fmt_size(size)
            self.tree_disk.item(item, values=v)
            if path != "/cache":
                total += max(0, size)
        self.lbl_disk.configure(text="合计（不含切片缓存）: %s" % fmt_size(total))
        self.add_event("统计了全部目录: 合计 %s（不含缓存）" % fmt_size(total))

    def show_disk_rows(self):
        """先把固定的目录列表画出来（不发任何网络请求，秒出）。"""
        self.tree_disk.delete(*self.tree_disk.get_children())
        self.dir_rows = {}
        for path, name, desc in REMOTE_DIRS:
            item = self.tree_disk.insert("", "end",
                                         values=("%s  (%s)" % (name, path), desc, "", ""))
            self.dir_rows[path] = item

    def on_dir_select(self, _e=None):
        self.load_dir_files()

    def load_dir_files(self):
        sel = self.tree_disk.selection()
        if not sel or not self.files:
            return
        label = self.tree_disk.item(sel[0], "values")[0]
        path = label[label.rfind("(") + 1:-1]
        if self.dir_cache.get(path):
            self.fill_dir_files(path, self.dir_cache[path])
            return
        self.lbl_disk.configure(text="正在读 %s …" % path)

        def work():
            try:
                files = self.files.list_dir(path)
                self.dir_cache[path] = files
                self.q.put(("dirfiles", (path, files)))
            except Exception as exc:
                log_exc("dirfiles")
                self.q.put(("dirfiles", (path, [])))

        threading.Thread(target=work, daemon=True).start()

    def fill_dir_files(self, path, files):
        self.cur_dir = path
        self.dir_files = files
        total = sum(f[1] for f in files if not f[3])
        n = len([f for f in files if not f[3]])
        item = self.dir_rows.get(path)
        if item:
            v = list(self.tree_disk.item(item, "values"))
            v[2] = str(n)
            v[3] = fmt_size(total)
            self.tree_disk.item(item, values=v)
        self.lbl_disk.configure(text="%s: %d 个文件, 合计 %s" % (path, n, fmt_size(total)))
        self.tree_files.delete(*self.tree_files.get_children())
        for name, size, when, isdir in sorted(files, key=lambda x: (-x[1])):
            self.tree_files.insert("", "end", values=(name + ("/" if isdir else ""),
                                                      "" if isdir else fmt_size(size), when))
        self.add_event("读了 %s: %d 个文件 %s" % (path, n, fmt_size(total)))

    def _sub_of(self, path):
        for p, name, _d in REMOTE_DIRS:
            if p == path:
                return name
        return "其它"

    def dl_selected_files(self):
        sel = self.tree_files.selection()
        if not sel or not self.files or not self.cur_dir:
            return
        names = [self.tree_files.item(i, "values")[0].rstrip("/") for i in sel]
        sub = self._sub_of(self.cur_dir)
        self.set_status("正在下载 %d 个文件…" % len(names))
        threading.Thread(target=self._dl, args=(self.cur_dir, sub, names), daemon=True).start()

    def del_selected_files(self):
        sel = self.tree_files.selection()
        if not sel or not self.files or not self.cur_dir:
            return
        names = [self.tree_files.item(i, "values")[0].rstrip("/") for i in sel]
        total = 0
        for i in sel:
            v = self.tree_files.item(i, "values")[1]
            if v.endswith("GB"):
                total += float(v[:-3]) * 1024
            elif v.endswith("MB"):
                total += float(v[:-3])
            elif v.endswith("KB"):
                total += float(v[:-3]) / 1024
        if not messagebox.askyesno("真的要删吗",
                                   "要从打印机里删掉 %d 个文件（约 %.1f MB）吗？\n\n删了就没了，"
                                   "想留的话先下载。" % (len(names), total)):
            return
        self.set_status("正在删 %d 个文件…" % len(names))

        def work():
            ok = 0
            for name in names:
                try:
                    self.files.delete(self.cur_dir, name)
                    ok += 1
                except Exception as exc:
                    log("删 %s 失败: %s" % (name, exc))
            self.q.put(("dl", "删掉了 %d / %d 个文件" % (ok, len(names))))
            self.q.put(("dirfiles", (self.cur_dir, self.files.list_dir(self.cur_dir))))

        threading.Thread(target=work, daemon=True).start()

    # ---------------- 控制 ----------------
    def need_link(self):
        if not self.link or not self.link.connected:
            messagebox.showinfo("先连打印机", "先点「连接」。")
            return False
        return True

    def do_pause(self):
        if self.need_link():
            self.link.pause()

    def do_resume(self):
        if self.need_link():
            self.link.resume()

    def do_stop(self):
        if not self.need_link():
            return
        if messagebox.askyesno("确定要停吗", "停止打印会把这盘直接废掉，\n已经打的部分救不回来。\n\n真的要停吗？"):
            self.link.stop_print()

    def do_speed(self, lvl):
        if self.need_link():
            self.link.set_speed(lvl)

    def do_light(self, mode):
        if self.need_link():
            self.link.set_light(mode)

    def save_light_opts(self):
        self.cfg["autolight"] = bool(self.var_autolight.get())
        try:
            d = int(float(self.var_lightdelay.get() or 0))
        except (TypeError, ValueError):
            d = 0
        d = max(0, min(3600, d))
        self.cfg["autolight_delay"] = d
        self.var_lightdelay.set(str(d))
        save_cfg(self.cfg)

    def auto_light_off(self):
        """打完自动关灯。

        ⚠️ 不要去判断「灯现在是不是开着」—— 实测上报的 lights_report 会滞后几秒，
        拿旧状态判断会误判成「本来就是关的」然后跳过（自检抓到的 bug）。
        直接发 off 就行, 关着的灯再关一次没有任何副作用。
        """
        if not self.link or not self.link.connected:
            self.add_event("自动关灯：打印机没连上，这次跳过")
            return
        self.link.set_light("off")
        self.add_event("自动关灯：发出了 灯光 -> off")

    def test_autooff(self):
        """自检用（--test-autooff）: 先把灯打开, 再走一遍自动关灯。"""
        if not self.link or not self.link.connected:
            self.add_event("自检 autooff：打印机没连上，跳过")
            return
        self.add_event("自检 autooff：先把灯打开")
        self.link.set_light("on")
        self.after(6000, self.auto_light_off)

    def do_toggle_timelapse(self):
        if not self.need_link():
            return
        cur = (self.last_state.get("ipcam") or {}).get("timelapse") == "enable"
        self.link.timelapse(not cur)

    def do_toggle_record(self):
        if not self.need_link():
            return
        cur = (self.last_state.get("ipcam") or {}).get("ipcam_record") == "enable"
        self.link.record(not cur)

    def load_objects(self):
        if not self.files:
            messagebox.showinfo("先连打印机", "先点「连接」。")
            return
        task = self.last_state.get("gcode_file") or self.last_state.get("subtask_name") or ""
        if not task:
            messagebox.showinfo("没有正在打的文件", "打印机没报当前文件，等它开始打了再读。")
            return
        self.lbl_obj.configure(text="正在读…")

        def work():
            try:
                name = task if task.lower().endswith(".3mf") else task + ".3mf"
                data = self.files.read_bytes("/cache", name)
                zf = zipfile.ZipFile(io.BytesIO(data))
                target = next((n for n in zf.namelist() if n.lower().endswith("slice_info.config")), None)
                objs = []
                if target:
                    root = ET.fromstring(zf.read(target))
                    for ob in root.iter("object"):
                        objs.append((ob.get("identify_id"), ob.get("name"), ob.get("skipped")))
                self.q.put(("objects", (name, objs)))
            except Exception as exc:
                log("读零件清单失败: %s: %s" % (type(exc).__name__, exc))
                self.q.put(("objects", (task, None)))

        threading.Thread(target=work, daemon=True).start()

    def fill_objects(self, name, objs):
        self.tree_obj.delete(*self.tree_obj.get_children())
        self.objects = objs or []
        if objs is None:
            self.lbl_obj.configure(text="没读到 %s（可能不在打印机的 /cache 里）" % name)
            return
        skipped = set(self.last_state.get("s_obj") or [])
        for oid, oname, osk in objs:
            state = "已跳过" if str(oid) in {str(x) for x in skipped} else "在打"
            self.tree_obj.insert("", "end", values=(oid, oname, state))
        self.lbl_obj.configure(text="共 %d 个零件" % len(objs))
        self.add_event("读到 %s 的零件清单: %d 个" % (name, len(objs)))

    def do_skip(self):
        if not self.need_link():
            return
        sel = self.tree_obj.selection()
        if not sel:
            messagebox.showinfo("先选零件", "在上面的列表里点要跳过的零件。")
            return
        ids = []
        for i in sel:
            try:
                ids.append(int(self.tree_obj.item(i, "values")[0]))
            except (TypeError, ValueError):
                pass
        if not ids:
            return
        names = ", ".join(str(self.tree_obj.item(i, "values")[1]) for i in sel)
        if messagebox.askyesno("跳过零件", "要跳过这些零件吗？\n\n%s\n\n跳过之后它就不打了。" % names):
            self.link.skip_objects(ids)

    # ---------------- 网页（给平板看） ----------------
    def web_state(self):
        """这个是在 HTTP 线程里被调的 —— 只能读数据，不许碰任何 tkinter 控件。"""
        st = self.link.snapshot() if self.link else {}
        gs = st.get("gcode_state", "?")
        try:
            pct = int(st.get("mc_percent", 0))
        except (TypeError, ValueError):
            pct = 0
        total = st.get("total_layer_num") or 0
        trays = []
        for unit in ((st.get("ams") or {}).get("ams") or []):
            for tr in (unit.get("tray") or []):
                if tr.get("tray_type"):
                    trays.append(tr["tray_type"])
        vt = st.get("vt_tray") or {}
        if vt.get("tray_type"):
            trays.append(vt["tray_type"])
        hms = st.get("hms") or []
        return {
            "state": STATE_CN.get(gs, gs),
            "task": st.get("subtask_name") or st.get("gcode_file") or "",
            "stage": stage_name(st.get("stg_cur")),
            "file": st.get("gcode_file") or st.get("subtask_name") or "",
            "pct": pct,
            "left": fmt_left(st.get("mc_remaining_time", 0)),
            "eta": eta_text(st.get("mc_remaining_time", 0)),
            "layer": ("%s / %s" % (st.get("layer_num", 0), total)) if total else "—",
            "nozzle": "%.1f / %.0f" % (st.get("nozzle_temper", 0),
                                       st.get("nozzle_target_temper", 0)),
            "bed": "%.1f / %.0f" % (st.get("bed_temper", 0), st.get("bed_target_temper", 0)),
            "chamber": "%.1f" % (st.get("chamber_temper", 0),),
            "cool": self.cool_text,
            "layer_n": self.cur_layer_n(),
            "layer_info": self.layer_info_text(),
            "layers_ready": len(self.layers),
            "marker_src": self.marker_src.get(),
            "marker_px": ("%.0f, %.0f" % self.marker_px) if self.marker_px else "",
            "marker_mm": ("%.1f, %.1f" % self.marker_mm()) if self.marker_mm() else "",
            "calib_n": len(self.calib),
            "plate_edge_y": self.plate_edge_y,
            "cal_x": list(self.cal_x) if self.cal_x else [],
            "cal_y": list(self.cal_y) if self.cal_y else [],
            "toast": self.toast or {},
            "conn": bool(self.link and getattr(self.link, "connected", False)),
            "nozzle_now": num(st.get("nozzle_temper")),
            "nozzle_tgt": num(st.get("nozzle_target_temper")),
            "bed_now": num(st.get("bed_temper")),
            "bed_tgt": num(st.get("bed_target_temper")),
            "chamber_num": num(st.get("chamber_temper")),
            "fan_model": num(st.get("cooling_fan_speed")),
            "fan_aux": num(st.get("big_fan1_speed")),
            "fan_hotend": num(st.get("heatbreak_fan_speed")),
            "cam_n": (self.cam.frames if self.cam else -1),
            "cam_age": (round(self.cam.age(), 1) if self.cam else -1),
            "misc": "风扇 模型 %s%% / 辅助 %s%% / 热端 %s%%　WiFi %s　耗材 %s　%s" % (
                st.get("cooling_fan_speed", "?"), st.get("big_fan1_speed", "?"),
                st.get("heatbreak_fan_speed", "?"), st.get("wifi_signal", "?"),
                "/".join(trays) or "没检测到",
                ("有 %d 条健康提示" % len(hms)) if hms else "没有异常提示"),
        }

    def web_jpeg(self):
        return self.cam.grab_jpeg() if self.cam else None

    def web_annot_jpeg(self):
        """把画好识别框的画面发给浏览器。"""
        jpeg = self.cam.grab_jpeg() if self.cam else None
        if not jpeg:
            return None
        return annotate_jpeg(jpeg, self.marker_px, self.plate_edge_y,
                             blobs=self.marker_blobs, note=self.marker_status_text())

    def save_recog_shot(self, jpeg=None):
        """把「画了识别框的画面」存一份到 RECOG_DIR（只留最近 RECOG_KEEP 张）。

        这个只在后台线程/按钮里调，只碰 PIL 和文件，不碰 tkinter。
        """
        jpeg = jpeg or (self.cam.grab_jpeg() if self.cam else None)
        if not jpeg:
            return None
        data = annotate_jpeg(jpeg, self.marker_px, self.plate_edge_y,
                             blobs=self.marker_blobs, note=self.marker_status_text())
        if not data:
            return None
        try:
            os.makedirs(RECOG_DIR, exist_ok=True)
            name = "识别_%s.jpg" % datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
            path = os.path.join(RECOG_DIR, name)
            with open(path, "wb") as f:
                f.write(data)
            old = sorted(x for x in os.listdir(RECOG_DIR)
                         if x.startswith("识别_") and x.endswith(".jpg"))
            for x in old[:-RECOG_KEEP]:
                try:
                    os.remove(os.path.join(RECOG_DIR, x))
                except OSError:
                    pass
            return path
        except OSError:
            log_exc("save_recog_shot")
            return None

    def marker_status_text(self):
        """识别结果那一行字（电脑上看板的标签和浏览器上的黑条共用）。"""
        if self.marker_src.get().startswith("假"):
            mm = self.marker_mm()
            return ("假标记（演示）：盘上 (%.0f, %.0f) mm　—— 编出来的，只看链路通不通"
                    % mm) if mm else "假标记：等层图算好"
        bits = []
        if self.marker_px:
            bits.append("蓝标 %d点 (%.0f,%.0f)" % (self.marker_nblobs,
                                                 self.marker_px[0], self.marker_px[1]))
        else:
            bits.append("没抓到蓝标")
        bits.append(("前沿 y=%.0f" % self.plate_edge_y) if self.plate_edge_y else "没抓到前沿")
        if self.cal_x:
            bits.append("cal_x=(%s)" % ", ".join(
                "—" if v is None else "%.0f" % v for v in self.cal_x))
        if self.cal_y:
            bits.append("cal_y=(%s)" % ", ".join(
                "—" if v is None else "%.0f" % v for v in self.cal_y))
        mm = self.marker_mm()
        if mm:
            bits.append("→ 盘上 (%.0f, %.0f) mm" % mm)
        elif self.cal_x and self.cal_y:
            bits.append("→ 换算失败")
        return "　".join(bits)

    def web_chart(self):
        return {"samples": [[round(float(x[1]), 1), round(float(x[2]), 1),
                             round(float(x[3]), 1), round(float(x[4]), 1)]
                            for x in self.samples]}

    def web_events(self):
        return {"lines": list(self.events[-300:])}

    def web_raw(self):
        st = self.link.snapshot() if self.link else {}
        return {"lines": ["%-22s %s" % (k, json.dumps(v, ensure_ascii=False)[:180])
                          for k, v in sorted(st.items())]}

    def web_reply(self):
        return {"lines": list(self.reply_lines[-60:])}

    def web_history(self, refresh=False):
        """延时摄影列表。第一次（或点了重新读取）才去打印机取，取完缓存住。"""
        if self.files and (refresh or not self.hist_cache) and not self.hist_loading:
            self.hist_loading = True
            files = self.files

            def work():
                try:
                    rows = files.list_dir("/timelapse")
                    vids = [x for x in rows if x[0].lower().endswith(".avi")]
                    vids.sort(key=lambda x: x[0])
                    self.hist_cache = vids
                    self.q.put(("msg", "网页读到 %d 段延时摄影" % len(vids)))
                except Exception:
                    log_exc("web history")
                finally:
                    self.hist_loading = False

            threading.Thread(target=work, daemon=True).start()
        out = []
        for name, size, when, isdir in self.hist_cache:
            m = re.match(r"video_(\d{4})-(\d{2})-(\d{2})_(\d{2})-(\d{2})-(\d{2})", name)
            stamp = ("%s-%s-%s %s:%s" % m.groups()[:5]) if m else when
            out.append({"name": name, "size": fmt_size(size), "when": stamp})
        return {"files": out}

    def web_thumb(self, name):
        if not self.files or not name:
            return None
        try:
            return self.files.read_bytes("/timelapse/thumbnail", name)
        except Exception as exc:
            log("网页取封面失败 %s: %s" % (name, exc))
            return None

    def web_file(self, rdir, name):
        if not self.files or not name:
            return None
        local = os.path.join(DL_ROOT, self._sub_of(rdir), os.path.basename(name))
        if not os.path.exists(local):
            self.files.download(rdir, name, local)
        return local

    def web_cmd(self, q):
        self.q.put(("web_cmd", q))

    def web_pass_ok(self, code):
        want = web_pass_read()
        return bool(want) and str(code or "").strip() == want

    def web_cookie(self):
        return hashlib.sha256(("bambu-dash|" + web_pass_read()).encode("utf-8")).hexdigest()

    def web_logged(self, cookie_hdr):
        return ("bdk=" + self.web_cookie()) in (cookie_hdr or "")

    def web_cal(self, q):
        """网页上点「喷嘴在盘某角」：先在这边看一眼有没有标记和盘子前沿，再丢给主线程记。"""
        table = {"lf": ("左前", 0, 0), "lb": ("左后", 0, 256),
                 "rf": ("右前", 256, 0), "rb": ("右后", 256, 256)}
        t = table.get(q.get("corner", ""), None)
        if not t:
            return {"ok": False, "msg": "角的名字不对"}
        if not self.marker_px:
            return {"ok": False, "msg": "还没抓到标记：先在电脑上看板切到「摄像头·蓝标」，"
                                        "等黄框套住喷头那块红贴纸"}
        if not self.plate_edge_y:
            return {"ok": False, "msg": "还没抓到盘子前沿，等画面刷新一下再点"}
        self.q.put(("web_cal", t))
        return {"ok": True, "msg": "记下%s：贴纸 x=%.0f、盘子前沿 y=%.0f"
                                   % (t[0], self.marker_px[0], self.plate_edge_y)}

    def run_web_cal(self, t):
        self.record_corner(*t)

    def run_web_cmd(self, q):
        if not self.link:
            return
        c = q.get("c")
        if c == "pause":
            self.link.pause()
        elif c == "resume":
            self.link.resume()
        elif c == "stop":
            self.link.stop_print()
        elif c == "speed":
            try:
                self.link.set_speed(int(q.get("v", 2)))
            except (TypeError, ValueError):
                pass
        elif c == "light":
            self.link.set_light("on" if q.get("v") == "on" else "off")

    def web_light(self, on):
        # 交给主线程去发 —— 连接和 tkinter 都不让 HTTP 线程碰
        self.q.put(("web_light", bool(on)))

    # ---------------- 平板二维码 ----------------
    def qr_path(self):
        return os.path.join(HERE, "平板二维码.png")

    def save_qr_file(self):
        """把二维码存成图片，方便他直接在电脑上打开。"""
        url = self.web_url or ("http://%s:%d" % (local_subnet() or "127.0.0.1", WEB_PORT))
        img = make_qr(url)
        if img is None:
            log("没装 qrcode，二维码没生成（py -m pip install qrcode -i 清华源）")
            return
        try:
            img.save(self.qr_path())
            log("二维码存到 %s （内容: %s）" % (self.qr_path(), url))
        except OSError:
            log_exc("save_qr_file")

    def show_qr(self):
        url = self.web_url or ("http://%s:%d" % (local_subnet() or "127.0.0.1", WEB_PORT))
        if self.qr_win is not None and self.qr_win.winfo_exists():
            self.qr_win.lift()
            return
        img = make_qr(url)
        if img is None or ImageTk is None:
            messagebox.showinfo("二维码", "没装 qrcode 库。\n\n在平板浏览器里手输这个地址也行:\n" + url)
            return
        win = tk.Toplevel(self)
        self.qr_win = win
        win.title("平板扫这个")
        win.configure(bg=BG)
        try:
            self.qr_photo = ImageTk.PhotoImage(img)
        except Exception:
            log_exc("qr photo")
            return
        ttk.Label(win, text="微信 / 相机扫这个，直接进看板网页").pack(pady=(14, 8))
        lbl = tk.Label(win, image=self.qr_photo, bg="white", bd=0)
        lbl.pack(padx=20)
        ttk.Label(win, text=url).pack(pady=(10, 4))
        ttk.Label(win, text="平板要和这台电脑连同一个 WiFi", foreground=DIM).pack(pady=(0, 10))
        ttk.Button(win, text="存成图片", command=self.save_qr_file).pack(pady=(0, 14))
        win.transient(self)

    # ---------------- 关闭 ----------------
    def on_close(self):
        try:
            self.stop_cam()
            if self.link:
                self.link.stop()
            if self.files:
                self.files.close()
        except Exception:
            pass
        self.destroy()


# --------------------------------------------------------------------------- #
#  给平板看的网页服务
# --------------------------------------------------------------------------- #
class WebHandler(http.server.BaseHTTPRequestHandler):
    app = None

    def log_message(self, *args):
        pass

    def _send(self, code, ctype, body, cookie=None):
        try:
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            if cookie:
                self.send_header("Set-Cookie", cookie)
            self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
            self.send_header("Pragma", "no-cache")
            self.send_header("Expires", "0")
            self.end_headers()
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _json(self, obj):
        try:
            self._send(200, "application/json; charset=utf-8",
                       json.dumps(obj, ensure_ascii=False).encode("utf-8"))
        except Exception:
            log_exc("web json")

    def _q(self, key):
        if "?" not in self.path:
            return ""
        qs = urllib.parse.parse_qs(self.path.split("?", 1)[1])
        return (qs.get(key) or [""])[0]

    def _send_file(self, rdir, name):
        """把打印机里的文件下到本地再发出去（视频几十兆，分块发）。"""
        local = self.app.web_file(rdir, name)
        if not local or not os.path.exists(local):
            self._send(404, "text/plain; charset=utf-8", b"404")
            return
        size = os.path.getsize(local)
        base = os.path.basename(local)
        try:
            self.send_response(200)
            self.send_header("Content-Type", "application/octet-stream")
            self.send_header("Content-Length", str(size))
            self.send_header("Content-Disposition",
                             "attachment; filename*=UTF-8''" + urllib.parse.quote(base))
            self.end_headers()
            with open(local, "rb") as f:
                while True:
                    chunk = f.read(65536)
                    if not chunk:
                        break
                    self.wfile.write(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def do_GET(self):
        path = self.path.split("?")[0]
        try:
            # ---- 访问码门禁：除了首页和登录接口，别的都得先过这一关 ----
            if path == "/api/login":
                if self.app.web_pass_ok(self._q("code")):
                    self._send(200, "application/json; charset=utf-8",
                               json.dumps({"ok": True}, ensure_ascii=False).encode("utf-8"),
                               cookie="bdk=%s; Path=/; Max-Age=2592000" % self.app.web_cookie())
                else:
                    self._json({"ok": False, "msg": "访问码不对"})
                return
            if path != "/" and not self.app.web_logged(self.headers.get("Cookie", "")):
                self._send(401, "application/json; charset=utf-8",
                           json.dumps({"need_login": True, "msg": "请先输入访问码"},
                                      ensure_ascii=False).encode("utf-8"))
                return
            if path == "/":
                self._send(200, "text/html; charset=utf-8", WEB_HTML.encode("utf-8"))
            elif path == "/api/state":
                self._json(self.app.web_state())
            elif path == "/api/chart":
                self._json(self.app.web_chart())
            elif path == "/api/events":
                self._json(self.app.web_events())
            elif path == "/api/cal":
                self._json(self.app.web_cal({k: v[0] for k, v in
                                  urllib.parse.parse_qs(self.path.split("?", 1)[1]).items()}))
            elif path == "/api/raw":
                self._json(self.app.web_raw())
            elif path == "/api/reply":
                self._json(self.app.web_reply())
            elif path == "/api/history":
                self._json(self.app.web_history("r=1" in self.path))
            elif path == "/api/thumb":
                data = self.app.web_thumb(self._q("name"))
                if data:
                    self._send(200, "image/jpeg", data)
                else:
                    self._send(204, "image/jpeg", b"")
            elif path == "/api/file":
                self._send_file(self._q("dir") or "/timelapse", self._q("name"))
            elif path == "/api/cam_annot.jpg":
                data = self.app.web_annot_jpeg()
                if data:
                    self._send(200, "image/jpeg", data)
                else:
                    self._send(204, "image/jpeg", b"")
            elif path == "/api/layer.png":
                n = self._q("n")
                try:
                    idx = int(n)
                except (TypeError, ValueError):
                    idx = self.app.cur_layer_n()
                data = self.app.web_layer_png(idx)
                if data:
                    self._send(200, "image/png", data)
                else:
                    self._send(204, "image/png", b"")
            elif path == "/api/cmd":
                self.app.web_cmd({k: v[0] for k, v in
                                  urllib.parse.parse_qs(self.path.split("?", 1)[1]).items()})
                self._json({"ok": True})
            elif path == "/api/cam.jpg":
                jpeg = self.app.web_jpeg()
                if jpeg:
                    self._send(200, "image/jpeg", jpeg)
                else:
                    self._send(204, "image/jpeg", b"")
            elif path == "/api/light":
                self.app.web_light("on=1" in self.path)
                self._json({"ok": True})
            else:
                self._send(404, "text/plain; charset=utf-8", b"404")
        except Exception:
            log_exc("web " + path)


def start_web(app, port=WEB_PORT):
    handler = type("BambuWebHandler", (WebHandler,), {"app": app})
    srv = http.server.ThreadingHTTPServer(("0.0.0.0", port), handler)
    srv.daemon_threads = True
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv


# --------------------------------------------------------------------------- #
#  自检
# --------------------------------------------------------------------------- #
def selftest():
    print("== Bambu 看板自检 ==")
    ok = True
    serial, code = read_studio_conf()
    print("1) 凭据: 序列号=%s 访问码=%s" % (serial, "有" if code else "没有"))
    if not (serial and code):
        return 1
    ips = scan_for_printer(logf=print)
    print("2) 扫描: %s" % ips)
    if not ips:
        return 1
    ip = ips[0]

    q = queue.Queue()
    link = PrinterLink(ip, serial, code, q)
    link.start()
    t0 = time.time()
    while time.time() - t0 < 15 and not link.state:
        time.sleep(0.3)
    st = link.snapshot()
    print("3) MQTT: %d 个字段, 完整快照=%s" % (len(st), link.full_seen))
    if st:
        for k in ("gcode_state", "mc_percent", "nozzle_temper", "bed_temper", "subtask_name",
                  "gcode_file"):
            print("     %-16s = %s" % (k, st.get(k)))
    else:
        ok = False
    t0 = time.time()
    while time.time() - t0 < 5 and not link.version:
        time.sleep(0.2)
    prod = ""
    for m in (link.version or {}).get("module", []):
        if m.get("product_name"):
            prod = m["product_name"]
    print("4) 型号: %s" % (prod or "(没拿到)"))
    ok = ok and bool(prod)
    link.stop()

    print("5) 文件: ", end="")
    try:
        pf = PrinterFiles(ip, code, q)
        rows = pf.list_dir("/timelapse")
        total = sum(r[1] for r in rows)
        print("%d 个文件, 合计 %s" % (len(rows), fmt_size(total)))
        pf.close()
    except Exception as exc:
        print("失败: %s" % exc)
        ok = False

    if Image is None:
        print("6) 摄像头: 跳过（没装 Pillow）")
    else:
        cq = queue.Queue()
        cam = CamLink(ip, code, cq)
        cam.start()
        t0 = time.time()
        got = None
        while time.time() - t0 < 25:
            try:
                kind, payload = cq.get(timeout=1)
            except queue.Empty:
                continue
            if kind == "cam":
                got = payload
                break
        if got:
            thumb, n = got
            os.makedirs(SHOT_DIR, exist_ok=True)
            p = os.path.join(SHOT_DIR, "自检.jpg")
            with open(p, "wb") as f:
                f.write(cam.grab_jpeg())
            print("6) 摄像头: 第 %d 帧 %s -> %s" % (n, thumb.size, p))
        else:
            print("6) 摄像头: 没拿到画面")
            ok = False
        cam.stop()
    print("== 结果: %s ==" % ("全部通过" if ok else "有失败项"))
    return 0 if ok else 1


def main():
    if "--selftest" in sys.argv:
        return selftest()
    log("---- 启动 ----")
    App().mainloop()
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception:
        log("!! 启动就崩了:\n" + traceback.format_exc())
        raise
