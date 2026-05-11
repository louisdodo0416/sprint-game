const canvas = document.getElementById('gameCanvas');
const ctx = canvas.getContext('2d');

const TRACK_HEIGHT = 500;
const LANE_HEIGHT = TRACK_HEIGHT / 4;
const TRACK_LENGTH = 6000;          // px — 60 px/m; calibrated so AI finish ~10.0–11.0 s at 60 fps
const RUNNER_H = 48;
const SPEED_BOOST = 2.2;
const SPEED_DISPLAY_SCALE = 2.23694; // px/frame → mph display (1 m/s × 2.23694)
const WR_MS = 9580;                  // Usain Bolt world record in ms
const CADENCE_MAX = 10;

// Start and end values — everything between is a continuous curve, no hard phase switches
const CFG_START = { target: 4.8, tol: 0.8, penaltyLow: 0.9988, penaltyHigh: 0.9993, maxSpeed: 7.5,  decay: 0.985 };
const CFG_END   = { target: 6.5, tol: 0.6, penaltyLow: 0.9983, penaltyHigh: 0.9988, maxSpeed: 13.8, decay: 0.988 };

const lerp = (a, b, t) => a + (b - a) * t;
const smoothstep = (e0, e1, x) => { const t = Math.max(0, Math.min(1, (x - e0) / (e1 - e0))); return t * t * (3 - 2 * t); };

// Returns config interpolated continuously across the full race — no discrete phase boundaries.
// Speed ceiling rises from the gun; cadence sweet-spot begins shifting at 10 m.
function getCfg(distM) {
  const tSpeed   = Math.min(1, Math.pow(distM / 55,  0.45)); // ceiling peaks at 55 m
  const tCadence = smoothstep(5, 60, distM);
  return {
    label:       distM < 40 ? 'DRIVE' : 'MAX VELOCITY',
    target:      lerp(CFG_START.target,      CFG_END.target,      tCadence),
    tol:         lerp(CFG_START.tol,         CFG_END.tol,         tCadence),
    penaltyLow:  lerp(CFG_START.penaltyLow,  CFG_END.penaltyLow,  tCadence),
    penaltyHigh: lerp(CFG_START.penaltyHigh, CFG_END.penaltyHigh, tCadence),
    maxSpeed:    lerp(CFG_START.maxSpeed,     CFG_END.maxSpeed,    tSpeed),
    decay:       lerp(CFG_START.decay,        CFG_END.decay,       tCadence),
  };
}

const LEAN_ZONE_MIN = 0.60, LEAN_ZONE_MAX = 0.95;
const LEAN_PERFECT_MIN = 0.72, LEAN_PERFECT_MAX = 0.88;

// ── State ─────────────────────────────────────────────────────────────────────
let state = 'title';
let cameraX = 0, frameCount = 0;
let finishOrder = [], lastKey = null;
let playerSpeed = 0, raceStartTime = 0, elapsedMs = 0;
let preRaceStart = 0, setDuration = 0, gunFiredAt = 0;
let reactionMs = 0, reactionRating = '', raceVarianceMs = 0;
let smoothedSpeed = 0;
let audioCtx = null;
let pressTimestamps = [], currentCadence = 0, needlePos = 0, needleTarget = 0;
let meterTarget = 4.0, meterTolerance = 1.2;
let activeCfg = getCfg(0); // continuously interpolated race config
let leanState = 'idle', leanResult = '', leanResultTimer = 0;
let dt = 1, lastTimestamp = 0;      // delta-time
let lbSaved = false, cachedLB = []; // leaderboard saved once per race

const runners = [
  { id: 0, lane: 0, x: 60, speed: 0, color: '#FF4DC4', name: 'Bolt',  ai: true,  baseAccel: 0.026, accel: 0.026, styleMag: 0.00, styleShape: 'steady', animTime: 0 },
  { id: 1, lane: 1, x: 60, speed: 0, color: '#ffd93d', name: 'Flash', ai: true,  baseAccel: 0.020, accel: 0.020, styleMag: 0.18, styleShape: 'late',   animTime: 0 },
  { id: 2, lane: 2, x: 60, speed: 0, color: '#6bcb77', name: 'Storm', ai: true,  baseAccel: 0.034, accel: 0.034, styleMag: 0.18, styleShape: 'early',  animTime: 0 },
  { id: 3, lane: 3, x: 60, speed: 0, color: '#4d96ff', name: 'YOU',   ai: false, animTime: 0 },
];
const player = runners[3];

function randomizeAIPeaks() {
  runners.filter(r => r.ai).forEach(r => {
    r.targetTime = 9750 + Math.random() * 450;  // 9.75–10.20 s
    r.accel      = r.baseAccel * (1 + (Math.random() * 0.30 - 0.15));
    r.animTime   = Math.random() * Math.PI * 2; // stagger starting phase so runners aren't in sync
  });
}
randomizeAIPeaks();

// ── Persistence ───────────────────────────────────────────────────────────────
function getPB() {
  const v = localStorage.getItem('sprint_pb');
  return v ? parseInt(v, 10) : null;
}
function savePB(ms) { localStorage.setItem('sprint_pb', ms); }

function getLB() {
  try { return JSON.parse(localStorage.getItem('sprint_lb') || '[]'); } catch { return []; }
}
function normalizeLBEntry(e) {
  return typeof e === 'number' ? { ms: e, name: null } : e;
}
function addToLB(ms, name) {
  const entries = getLB().map(normalizeLBEntry);
  entries.push({ ms, name });
  entries.sort((a, b) => a.ms - b.ms);
  const top10 = entries.slice(0, 10);
  localStorage.setItem('sprint_lb', JSON.stringify(top10));
  return top10;
}

// ── Audio ─────────────────────────────────────────────────────────────────────
function playGunshot() {
  if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  const t = audioCtx.currentTime, sr = audioCtx.sampleRate;

  const comp = audioCtx.createDynamicsCompressor();
  comp.threshold.value = -3; comp.knee.value = 3;
  comp.ratio.value = 20; comp.attack.value = 0.001; comp.release.value = 0.1;
  comp.connect(audioCtx.destination);

  // Crack — sharp high-frequency transient
  const crackBuf = audioCtx.createBuffer(1, Math.floor(sr*0.08), sr);
  const cd = crackBuf.getChannelData(0);
  for (let i=0;i<cd.length;i++) cd[i]=(Math.random()*2-1)*(1-i/cd.length);
  const crack = audioCtx.createBufferSource(); crack.buffer = crackBuf;
  const crackHp = audioCtx.createBiquadFilter(); crackHp.type='highpass'; crackHp.frequency.value=3000;
  const crackG = audioCtx.createGain(); crackG.gain.setValueAtTime(5, t); crackG.gain.exponentialRampToValueAtTime(0.001, t+0.07);
  crack.connect(crackHp); crackHp.connect(crackG); crackG.connect(comp); crack.start(t);

  // Body — mid-range bang
  const bodyBuf = audioCtx.createBuffer(1, Math.floor(sr*0.3), sr);
  const bd = bodyBuf.getChannelData(0);
  for (let i=0;i<bd.length;i++) bd[i]=Math.random()*2-1;
  const body = audioCtx.createBufferSource(); body.buffer = bodyBuf;
  const bodyBp = audioCtx.createBiquadFilter(); bodyBp.type='bandpass'; bodyBp.frequency.value=1000; bodyBp.Q.value=0.6;
  const bodyG = audioCtx.createGain(); bodyG.gain.setValueAtTime(3.5, t); bodyG.gain.exponentialRampToValueAtTime(0.001, t+0.22);
  body.connect(bodyBp); bodyBp.connect(bodyG); bodyG.connect(comp); body.start(t);

  // Thud — low-end pitch sweep
  const osc = audioCtx.createOscillator();
  osc.frequency.setValueAtTime(200, t); osc.frequency.exponentialRampToValueAtTime(25, t+0.1);
  const thudG = audioCtx.createGain(); thudG.gain.setValueAtTime(2.5, t); thudG.gain.exponentialRampToValueAtTime(0.001, t+0.14);
  osc.connect(thudG); thudG.connect(comp); osc.start(t); osc.stop(t+0.18);
}

// ── Reset ─────────────────────────────────────────────────────────────────────
function resetRace() {
  state = 'title'; cameraX = 0; frameCount = 0;
  finishOrder = []; lastKey = null;
  playerSpeed = 0; smoothedSpeed = 0; raceStartTime = 0; elapsedMs = 0;
  preRaceStart = 0; gunFiredAt = 0; reactionMs = 0; reactionRating = '';
  pressTimestamps = []; currentCadence = 0; needlePos = 0; needleTarget = 0;
  meterTarget = 4.0; meterTolerance = 1.2; activeCfg = getCfg(0);
  leanState = 'idle'; leanResult = ''; leanResultTimer = 0;
  lbSaved = false; cachedLB = [];
  runners.forEach(r => { r.x = 60; r.speed = 0; });
  player.animTime = 0;
  randomizeAIPeaks();
  lastTimestamp = 0;
  requestAnimationFrame(loop);
}

// ── Input ─────────────────────────────────────────────────────────────────────
canvas.addEventListener('mousedown', () => {
  if (state === 'title') {
    if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    state = 'marks'; preRaceStart = Date.now(); return;
  }
  if (state === 'idle') {
    if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    state = 'marks'; preRaceStart = Date.now(); return;
  }
  if (state === 'marks' || state === 'set') { state = 'false_start'; return; }
  if (state === 'gun') {
    const now = Date.now();
    reactionMs = now - gunFiredAt;
    const driveMax = CFG_START.maxSpeed;
    if      (reactionMs < 120) { playerSpeed = driveMax * 0.70; reactionRating = 'PERFECT'; }
    else if (reactionMs < 200) { playerSpeed = driveMax * 0.50; reactionRating = 'GREAT';   }
    else if (reactionMs < 300) { playerSpeed = driveMax * 0.28; reactionRating = 'GOOD';    }
    else                       { playerSpeed = 0;               reactionRating = 'SLOW';    }
    raceVarianceMs = Math.round((Math.random() - 0.5) * 160);
    raceStartTime = now; state = 'racing';
  }
});

document.addEventListener('keydown', (e) => {
  if (e.repeat) return;
  const key = e.key.toLowerCase();
  if (key === 'r' && (state === 'finished' || state === 'false_start' || state === 'gun' || state === 'racing')) { resetRace(); return; }
  if (e.key === ' ' && state === 'racing' && leanState === 'ready') {
    e.preventDefault();
    const t = ((player.x / TRACK_LENGTH) * 100 - 90) / 10;
    leanState = 'done'; leanResultTimer = Date.now();
    if      (t >= LEAN_PERFECT_MIN && t <= LEAN_PERFECT_MAX) { raceStartTime += 50;  leanResult = 'PERFECT LEAN!  −0.05s'; }
    else if (t >= LEAN_ZONE_MIN    && t <= LEAN_ZONE_MAX)    { raceStartTime += 20;  leanResult = 'GOOD LEAN  −0.02s';     }
    else if (t < LEAN_ZONE_MIN)                              { raceStartTime -= 30;  leanResult = 'TOO EARLY  +0.03s';     }
    else                                                     { raceStartTime -= 20;  leanResult = 'TOO LATE  +0.02s';      }
    return;
  }
  if (state !== 'racing') return;
  if (key !== 'a' && key !== 'd') return;
  if (key !== lastKey) {
    lastKey = key;
    pressTimestamps.push(Date.now());
    if (pressTimestamps.length > 6) pressTimestamps.shift();
    const szMin = (meterTarget - meterTolerance) / CADENCE_MAX;
    const szMax = (meterTarget + meterTolerance) / CADENCE_MAX;
    if (needlePos >= szMin && needlePos <= szMax) {
      playerSpeed = Math.min(playerSpeed + SPEED_BOOST, activeCfg.maxSpeed);
    } else if (Date.now() - raceStartTime > 1500) {
      const dist = needlePos < szMin ? szMin - needlePos : needlePos - szMax;
      playerSpeed *= 1 - Math.min(dist / 0.35, 1) * 0.03;
    }
  }
});

// ── Helpers ───────────────────────────────────────────────────────────────────
const laneY = lane => lane * LANE_HEIGHT + (LANE_HEIGHT - RUNNER_H) / 2;
const fmtTime = ms => (ms / 1000).toFixed(2) + 's';

// ── Pre-race ──────────────────────────────────────────────────────────────────
function updatePreRace() {
  const now = Date.now();
  if (state === 'marks' && now - preRaceStart > 1500) { state = 'set'; preRaceStart = now; setDuration = 1000 + Math.random() * 1500; }
  if (state === 'set'   && now - preRaceStart > setDuration) { state = 'gun'; gunFiredAt = Date.now(); playGunshot(); }
}

// ── Race update (delta-time aware) ────────────────────────────────────────────
function updateCadence() {
  const now = Date.now();
  while (pressTimestamps.length > 0 && now - pressTimestamps[0] > 2000) pressTimestamps.shift();
  let needleInput;
  if (pressTimestamps.length >= 2) {
    const span = pressTimestamps[pressTimestamps.length - 1] - pressTimestamps[0];
    const raw = (pressTimestamps.length - 1) / (span / 1000);
    const msSinceLast = now - pressTimestamps[pressTimestamps.length - 1];
    const avgInterval = span / (pressTimestamps.length - 1);
    currentCadence = msSinceLast > avgInterval * 1.2 ? Math.max(0, raw * avgInterval / msSinceLast) : raw;
    needleInput = raw;
  } else {
    currentCadence = Math.max(0, currentCadence - 0.04 * dt);
    needleInput = currentCadence;
  }
  needleTarget += (Math.min(needleInput / CADENCE_MAX, 1) - needleTarget) * 0.07 * dt;
  needlePos    += (needleTarget - needlePos) * 0.18 * dt;
}

function update() {
  frameCount += dt;
  elapsedMs = Date.now() - raceStartTime;

  updateCadence();

  const distM = (player.x / TRACK_LENGTH) * 100;
  activeCfg = getCfg(distM);

  // Animate cadence meter sweet-spot toward continuously moving targets
  meterTarget    += (activeCfg.target - meterTarget)    * 0.025 * dt;
  meterTolerance += (activeCfg.tol    - meterTolerance) * 0.025 * dt;

  // Cadence penalty (blended per-phase values)
  const sweetMin = activeCfg.target - activeCfg.tol;
  const sweetMax = activeCfg.target + activeCfg.tol;
  if (elapsedMs > 1500) {
    if      (currentCadence < sweetMin) playerSpeed *= Math.pow(activeCfg.penaltyLow,  dt);
    else if (currentCadence > sweetMax) playerSpeed *= Math.pow(activeCfg.penaltyHigh, dt);
  }

  // Continuously scaled decay and speed ceiling
  playerSpeed *= Math.pow(activeCfg.decay, dt);
  playerSpeed  = Math.min(playerSpeed, activeCfg.maxSpeed);

  // Fatigue (75-100m): compounding deceleration; good cadence offsets the drag
  const fatigueT = smoothstep(75, 100, distM);
  if (fatigueT > 0) {
    const inSweet = currentCadence >= sweetMin && currentCadence <= sweetMax;
    playerSpeed *= Math.pow(inSweet ? lerp(1, 0.9992, fatigueT) : lerp(1, 0.9982, fatigueT), dt);
    playerSpeed  = Math.min(playerSpeed, activeCfg.maxSpeed * lerp(1, inSweet ? 0.97 : 0.93, fatigueT));
  }

  player.speed    = playerSpeed;
  player.x       += player.speed * dt;
  player.animTime += 0.06 * playerSpeed * dt;

  runners.filter(r => r.ai).forEach(r => {
    const aiDistM    = (r.x / TRACK_LENGTH) * 100;
    const remainingPx = Math.max(1, TRACK_LENGTH - r.x);
    const remainingS  = Math.max(0.3, (r.targetTime - elapsedMs) / 1000);
    const paceSpeed   = Math.min(14, remainingPx / (remainingS * 60));

    // Style deviation: signed fraction of paceSpeed; averages ~0 over the race so targetTime is preserved
    let styleDev = 0;
    if (r.styleShape === 'early') styleDev = r.styleMag * paceSpeed * lerp( 1, -1, smoothstep(15, 65, aiDistM));
    if (r.styleShape === 'late')  styleDev = r.styleMag * paceSpeed * lerp(-1,  1, smoothstep(25, 80, aiDistM));

    const wobble    = Math.sin(frameCount * 0.04 + r.id * 1.3) * 0.12;
    const startupT  = smoothstep(0, 22, aiDistM);
    const rawTarget = Math.max(1, paceSpeed + styleDev);
    const aiTarget  = lerp(Math.min(rawTarget, 6.5), rawTarget, startupT) + wobble;
    r.speed    += (aiTarget - r.speed) * r.accel * dt;
    r.x        += r.speed * dt;
    if (r.x >= TRACK_LENGTH && elapsedMs < 9580) r.x = TRACK_LENGTH - 0.5;
    r.animTime += 0.06 * r.speed * dt;
  });

  cameraX = Math.max(0, player.x - canvas.width * 0.25);

  if (distM >= 90  && leanState === 'idle')  leanState = 'ready';
  if (distM >= 100 && leanState === 'ready') { leanState = 'missed'; raceStartTime -= 20; leanResult = 'NO LEAN  +0.02s'; leanResultTimer = Date.now(); }

  runners.forEach(r => {
    if (r.x >= TRACK_LENGTH && !finishOrder.find(f => f.id === r.id)) {
      const recordedTime = r.ai ? elapsedMs : Math.max(9590, elapsedMs + raceVarianceMs);
      finishOrder.push({ id: r.id, name: r.name, ai: r.ai, time: recordedTime });
      finishOrder.sort((a, b) => a.time - b.time);
      if (!r.ai && !lbSaved) {
        const pb = getPB();
        if (pb === null || recordedTime < pb) savePB(recordedTime);
        cachedLB = addToLB(recordedTime, 'YOU');
        lbSaved = true;
      }
    }
  });
  if (finishOrder.find(f => f.id === player.id)) state = 'finished';
}

// ── Drawing: track ────────────────────────────────────────────────────────────
function drawTrack() {
  for (let i = 0; i < 4; i++) {
    ctx.fillStyle = i % 2 === 0 ? '#d95f2b' : '#c45220';
    ctx.fillRect(0, i * LANE_HEIGHT, canvas.width, LANE_HEIGHT);
  }
  ctx.strokeStyle = 'rgba(255,255,255,0.90)'; ctx.lineWidth = 5;
  for (let i = 1; i < 4; i++) { ctx.beginPath(); ctx.moveTo(0, i * LANE_HEIGHT); ctx.lineTo(canvas.width, i * LANE_HEIGHT); ctx.stroke(); }
  ctx.strokeStyle = '#fff'; ctx.lineWidth = 5;
  ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(canvas.width, 0); ctx.moveTo(0, TRACK_HEIGHT); ctx.lineTo(canvas.width, TRACK_HEIGHT); ctx.stroke();

  ctx.textAlign = 'center';
  for (let m = 10; m <= 100; m += 10) {
    const sx = (m / 100) * TRACK_LENGTH - cameraX;
    if (sx < -20 || sx > canvas.width + 20) continue;
    ctx.strokeStyle = 'rgba(255,255,255,0.55)'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(sx, 0); ctx.lineTo(sx, TRACK_HEIGHT); ctx.stroke();
    ctx.fillStyle = '#fff'; ctx.font = 'bold 20px monospace'; ctx.textAlign = 'right';
    ctx.fillText(`${m}m`, sx - 5, 18);
  }
  const fx = TRACK_LENGTH - cameraX;
  if (fx > -30 && fx < canvas.width + 30) {
    const tH = TRACK_HEIGHT / 8;
    for (let row = 0; row < 8; row++) for (let col = 0; col < 5; col++) { ctx.fillStyle = (row + col) % 2 === 0 ? '#fff' : '#111'; ctx.fillRect(fx + col * 8, row * tH, 8, tH); }
  }
  const startX = 110 - cameraX;
  if (startX > -5 && startX < canvas.width + 5) {
    ctx.strokeStyle = '#fff'; ctx.lineWidth = 5;
    ctx.beginPath(); ctx.moveTo(startX, 0); ctx.lineTo(startX, TRACK_HEIGHT); ctx.stroke();
  }
}

// ── Drawing: runners ──────────────────────────────────────────────────────────
function drawRunner(r) {
  const sx = r.x - cameraX;
  if (sx < -50 || sx > canvas.width + 50) return;
  const y = laneY(r.lane);

  // Shadow
  ctx.fillStyle = 'rgba(0,0,0,0.18)';
  ctx.beginPath();
  ctx.ellipse(sx + 10, y + 75, 18, 5, 0, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = r.color;

  // Filled capsule segment from (ax,ay) to (bx,by), width w
  function seg(ax, ay, bx, by, w) {
    const len = Math.hypot(bx - ax, by - ay);
    ctx.save();
    ctx.translate((ax + bx) / 2, (ay + by) / 2);
    ctx.rotate(Math.atan2(by - ay, bx - ax));
    ctx.beginPath();
    ctx.roundRect(-len / 2, -w / 2, len, w, w / 2);
    ctx.fill();
    ctx.restore();
  }

  // Filled circle — head or joint filler
  function dot(x, y, r) { ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill(); }

  if (['idle', 'marks', 'set', 'gun'].includes(state)) {
    // ── Crouched "set" pose — weight forward over hands, hips raised ───────
    const gy = y + 74;                             // ground level
    const chX = sx +  8, chY = gy - 30;           // hip (body's highest point)
    const csX = sx + 26, csY = gy - 20;           // shoulder — torso nearly horizontal

    const cfKnX = sx + 22, cfKnY = gy - 18;       // front knee (bent under body)
    const cfFtX = sx + 16, cfFtY = gy -  6;       // front foot on front block
    const cbKnX = sx +  2, cbKnY = gy - 14;       // back knee (low, near ground)
    const cbFtX = sx -  2, cbFtY = gy -  3;       // back foot on back block

    const cfElX = sx + 32, cfElY = gy - 10;       // front arm elbow
    const cfHdX = sx + 34, cfHdY = gy -  2;       // front hand on track
    const cbElX = sx + 22, cbElY = gy - 10;       // back arm elbow
    const cbHdX = sx + 22, cbHdY = gy -  2;       // back hand on track

    seg(chX, chY, cfKnX, cfKnY, 11);  seg(cfKnX, cfKnY, cfFtX, cfFtY,  9); // front thigh+shin
    seg(chX, chY, cbKnX, cbKnY, 11);  seg(cbKnX, cbKnY, cbFtX, cbFtY,  9); // back thigh+shin
    seg(csX, csY, cfElX, cfElY,  8);  seg(cfElX, cfElY, cfHdX, cfHdY,  7); // front arm
    seg(csX, csY, cbElX, cbElY,  8);  seg(cbElX, cbElY, cbHdX, cbHdY,  7); // back arm
    seg(chX, chY, csX,   csY,   13);                                         // torso

    dot(chX, chY, 8);   dot(csX, csY, 7);
    dot(cfKnX, cfKnY, 6); dot(cbKnX, cbKnY, 6);
    dot(cfElX, cfElY, 5); dot(cbElX, cbElY, 5);
    dot(sx + 32, gy - 24, 8);  // head — forward, looking slightly down
  } else {
    // ── Running animation ─────────────────────────────────────────────────
    const hipX = sx + 14, hipY = y + 52;
    const shlX = sx + 23, shlY = y + 25;
    const hdX  = sx + 27, hdY  = y + 13;

    const lp    = (a, b, t) => a + (b - a) * t;
    const p     = Math.sin(r.animTime);
    const baseY = y + 74;

    const dA = Math.max(0,  p);
    const sA = Math.max(0, -p);
    const dB = Math.max(0, -p);
    const sB = Math.max(0,  p);

    const laKnX = hipX       + dA * 24 - sA * 16;
    const laKnY = hipY + 10  - dA * 18;
    const laFtX = hipX + 4   + dA * 22 - sA * 28;
    const laFtY = baseY      - dA *  8;

    const lbKnX = hipX       + dB * 24 - sB * 16;
    const lbKnY = hipY + 10  - dB * 18;
    const lbFtX = hipX + 4   + dB * 22 - sB * 28;
    const lbFtY = baseY      - dB *  8;

    const tA = (p + 1) * 0.5;
    const tB = (1 - p) * 0.5;

    const fwdElX = sx + 34, fwdElY = y + 32;
    const fwdHdX = sx + 26, fwdHdY = y + 22;
    const bckElX = sx + 10, bckElY = y + 32;
    const bckHdX = sx + 18, bckHdY = y + 46;

    const aaElX = lp(bckElX, fwdElX, tB), aaElY = lp(bckElY, fwdElY, tB);
    const aaHdX = lp(bckHdX, fwdHdX, tB), aaHdY = lp(bckHdY, fwdHdY, tB);
    const abElX = lp(bckElX, fwdElX, tA), abElY = lp(bckElY, fwdElY, tA);
    const abHdX = lp(bckHdX, fwdHdX, tA), abHdY = lp(bckHdY, fwdHdY, tA);

    seg(hipX, hipY, laKnX, laKnY, 11);  seg(laKnX, laKnY, laFtX, laFtY,  9);
    seg(hipX, hipY, lbKnX, lbKnY, 11);  seg(lbKnX, lbKnY, lbFtX, lbFtY,  9);
    seg(shlX, shlY, aaElX, aaElY,  8);  seg(aaElX, aaElY, aaHdX, aaHdY,  7);
    seg(shlX, shlY, abElX, abElY,  8);  seg(abElX, abElY, abHdX, abHdY,  7);
    seg(hipX, hipY, shlX, shlY, 13);

    dot(hipX, hipY, 8);   dot(shlX, shlY, 7);
    dot(laKnX, laKnY, 6); dot(lbKnX, lbKnY, 6);
    dot(aaElX, aaElY, 5); dot(abElX, abElY, 5);
    dot(hdX, hdY, 8);
  }

  ctx.font = 'bold 14px monospace'; ctx.textAlign = 'center';
  ctx.fillStyle = r.color;
  ctx.fillText(r.name, sx + 13, y - 5);
  const fi = finishOrder.findIndex(f => f.id === r.id);
  if (fi !== -1) { ctx.fillStyle = ['#ffd700','#c0c0c0','#cd7f32','#888'][fi]; ctx.font = 'bold 12px monospace'; ctx.fillText(['1st','2nd','3rd','4th'][fi], sx + 13, y - 18); }
}

// ── Drawing: cadence meter ────────────────────────────────────────────────────
function drawCadenceMeter() {
  const bx = 12, bw = canvas.width - 24, by = TRACK_HEIGHT + 20, bh = 22;
  ctx.fillStyle = 'rgba(0,0,0,0.62)'; ctx.fillRect(bx - 2, by - 16, bw + 4, bh + 20);
  ctx.fillStyle = '#888'; ctx.font = '10px monospace'; ctx.textAlign = 'left';
  ctx.fillText(activeCfg.label, bx, by - 3);

  const grad = ctx.createLinearGradient(bx, 0, bx + bw, 0);
  grad.addColorStop(0, 'rgba(77,150,255,0.30)'); grad.addColorStop(0.5, 'rgba(255,255,255,0.08)'); grad.addColorStop(1, 'rgba(233,69,96,0.30)');
  ctx.fillStyle = grad; ctx.fillRect(bx, by, bw, bh);

  const szMin = (meterTarget - meterTolerance) / CADENCE_MAX;
  const szMax = (meterTarget + meterTolerance) / CADENCE_MAX;
  const szx = bx + szMin * bw, szw = (szMax - szMin) * bw;
  ctx.fillStyle = 'rgba(80,210,100,0.30)'; ctx.fillRect(szx, by, szw, bh);
  ctx.strokeStyle = 'rgba(80,210,100,0.70)'; ctx.lineWidth = 1.5; ctx.strokeRect(szx, by, szw, bh);

  ctx.font = '9px monospace'; ctx.textAlign = 'center';
  ctx.fillStyle = 'rgba(80,210,100,0.9)';  ctx.fillText('SWEET SPOT', szx + szw / 2, by + bh - 5);
  if (szMin > 0.10) { ctx.fillStyle = 'rgba(120,150,255,0.75)'; ctx.fillText('TOO SLOW', bx + (szMin * bw) / 2, by + bh - 5); }
  if (szMax < 0.90) { ctx.fillStyle = 'rgba(255,110,110,0.75)'; ctx.fillText('TOO FAST', szx + szw + (bx + bw - szx - szw) / 2, by + bh - 5); }

  const nx = bx + needlePos * bw;
  const inSweet = needlePos >= szMin && needlePos <= szMax;
  ctx.fillStyle = inSweet ? '#6bcb77' : (needlePos < szMin ? '#4d96ff' : '#e94560');
  ctx.fillRect(nx - 2, by, 4, bh);
  ctx.beginPath(); ctx.moveTo(nx - 6, by); ctx.lineTo(nx + 6, by); ctx.lineTo(nx, by - 7); ctx.closePath(); ctx.fill();
  ctx.strokeStyle = 'rgba(255,255,255,0.22)'; ctx.lineWidth = 1; ctx.strokeRect(bx, by, bw, bh);
}

// ── Drawing: lean bar ─────────────────────────────────────────────────────────
function drawLeanBar() {
  if (leanState === 'idle') return;
  const distInFinish = Math.max(0, Math.min(((player.x / TRACK_LENGTH) * 100 - 90) / 10, 1));
  const bw = 400, bh = 22, bx = canvas.width / 2 - bw / 2, by = 72;
  ctx.fillStyle = 'rgba(0,0,0,0.70)'; ctx.fillRect(bx - 10, by - 22, bw + 20, bh + 32);
  if (leanState === 'ready') { ctx.fillStyle = '#ffd93d'; ctx.font = 'bold 12px monospace'; ctx.textAlign = 'center'; ctx.fillText('LEAN!  Press SPACE', canvas.width / 2, by - 8); }
  ctx.fillStyle = 'rgba(255,255,255,0.07)'; ctx.fillRect(bx, by, bw, bh);
  ctx.fillStyle = 'rgba(80,210,100,0.28)'; ctx.fillRect(bx + LEAN_ZONE_MIN * bw, by, (LEAN_ZONE_MAX - LEAN_ZONE_MIN) * bw, bh);
  ctx.fillStyle = 'rgba(255,215,0,0.45)'; ctx.fillRect(bx + LEAN_PERFECT_MIN * bw, by, (LEAN_PERFECT_MAX - LEAN_PERFECT_MIN) * bw, bh);
  ctx.font = '9px monospace'; ctx.textAlign = 'center';
  ctx.fillStyle = 'rgba(255,215,0,0.85)'; ctx.fillText('PERFECT', bx + (LEAN_PERFECT_MIN + LEAN_PERFECT_MAX) / 2 * bw, by + bh - 5);
  if (leanState === 'ready') {
    const nx = bx + distInFinish * bw;
    ctx.fillStyle = distInFinish >= LEAN_ZONE_MIN ? '#ffd700' : '#fff';
    ctx.fillRect(nx - 2, by, 4, bh);
    ctx.beginPath(); ctx.moveTo(nx - 6, by); ctx.lineTo(nx + 6, by); ctx.lineTo(nx, by - 7); ctx.closePath(); ctx.fill();
  }
  if ((leanState === 'done' || leanState === 'missed') && leanResultTimer > 0) {
    const age = Date.now() - leanResultTimer;
    if (age < 2500) {
      ctx.globalAlpha = Math.max(0, 1 - age / 2500);
      const rColors = { 'PERFECT LEAN!  −0.05s': '#ffd700', 'GOOD LEAN  −0.02s': '#6bcb77', 'TOO EARLY  +0.03s': '#ff6b6b', 'TOO LATE  +0.02s': '#aaa', 'NO LEAN  +0.02s': '#666' };
      ctx.fillStyle = rColors[leanResult] || '#fff'; ctx.font = 'bold 13px monospace'; ctx.textAlign = 'center';
      ctx.fillText(leanResult, canvas.width / 2, by + bh + 16);
      ctx.globalAlpha = 1;
    }
  }
  ctx.strokeStyle = 'rgba(255,255,255,0.28)'; ctx.lineWidth = 1; ctx.strokeRect(bx, by, bw, bh);
}

// ── Drawing: HUD ──────────────────────────────────────────────────────────────
function drawHUD() {
  // mph readout — smoothed to avoid per-keypress jitter
  smoothedSpeed += (playerSpeed - smoothedSpeed) * 0.08 * dt;
  const mps = (smoothedSpeed * SPEED_DISPLAY_SCALE).toFixed(1);
  const mpsColor = playerSpeed / activeCfg.maxSpeed > 0.75 ? '#e94560' : playerSpeed / activeCfg.maxSpeed > 0.45 ? '#ffd93d' : '#4d96ff';
  ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(12, TRACK_HEIGHT + 58, 130, 42);
  ctx.fillStyle = '#888'; ctx.font = '10px monospace'; ctx.textAlign = 'left'; ctx.fillText('SPEED', 16, TRACK_HEIGHT + 72);
  ctx.fillStyle = mpsColor; ctx.font = 'bold 22px monospace'; ctx.fillText(mps, 16, TRACK_HEIGHT + 94);
  ctx.fillStyle = '#666'; ctx.font = '11px monospace'; ctx.fillText('mph', 16 + ctx.measureText(mps).width + 4, TRACK_HEIGHT + 94);

  // Key indicators
  const nextKey = lastKey === 'a' ? 'D' : 'A';
  ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(canvas.width - 118, TRACK_HEIGHT + 58, 106, 42);
  ['A','D'].forEach((k, i) => {
    const isNext = k === nextKey && state === 'racing';
    ctx.fillStyle = isNext ? '#e94560' : 'rgba(255,255,255,0.10)';
    ctx.beginPath(); ctx.roundRect(canvas.width - 114 + i * 50, TRACK_HEIGHT + 62, 38, 34, 4); ctx.fill();
    ctx.fillStyle = isNext ? '#fff' : '#444'; ctx.font = 'bold 18px monospace'; ctx.textAlign = 'center';
    ctx.fillText(k, canvas.width - 95 + i * 50, TRACK_HEIGHT + 86);
  });

  // Distance
  const dist = Math.min((player.x / TRACK_LENGTH) * 100, 100).toFixed(1);
  ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(canvas.width / 2 - 65, TRACK_HEIGHT + 58, 130, 42);
  ctx.fillStyle = '#fff'; ctx.font = 'bold 13px monospace'; ctx.textAlign = 'center'; ctx.fillText(`${dist}m`, canvas.width / 2, TRACK_HEIGHT + 86);
  ctx.fillStyle = '#888'; ctx.font = '10px monospace'; ctx.fillText('/ 100m', canvas.width / 2, TRACK_HEIGHT + 72);

  // Timer
  const displayMs = state === 'finished' ? (finishOrder.find(f => f.id === player.id)?.time ?? elapsedMs) : elapsedMs;
  ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(canvas.width / 2 - 60, 10, 120, 34);
  ctx.fillStyle = state === 'finished' ? '#ffd700' : '#fff'; ctx.font = 'bold 20px monospace'; ctx.textAlign = 'center';
  ctx.fillText(fmtTime(displayMs), canvas.width / 2, 33);

  // Reaction rating (fades first 2s)
  if (reactionRating && elapsedMs < 2000) {
    ctx.globalAlpha = Math.max(0, 1 - elapsedMs / 2000);
    ctx.fillStyle = { PERFECT:'#ffd700', GREAT:'#6bcb77', GOOD:'#4d96ff', SLOW:'#aaa' }[reactionRating];
    ctx.font = 'bold 15px monospace'; ctx.textAlign = 'center';
    ctx.fillText(`${reactionRating}  ${fmtTime(reactionMs)} reaction`, canvas.width / 2, 58);
    ctx.globalAlpha = 1;
  }

  drawCadenceMeter();
  drawLeanBar();
}

// ── Drawing: pre-race overlay ─────────────────────────────────────────────────
function drawPreRaceOverlay() {
  const cx = canvas.width / 2, cy = TRACK_HEIGHT / 2;
  ctx.textAlign = 'center';

  if (state === 'idle') {
    ctx.fillStyle = 'rgba(0,0,0,0.58)'; ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.fillStyle = '#fff'; ctx.font = 'bold 22px monospace'; ctx.fillText('100M SPRINT', cx, cy - 22);
    ctx.font = '13px monospace'; ctx.fillStyle = '#aaa';
    ctx.fillText('Click to get on your marks', cx, cy + 8);
    ctx.fillText('React to the gun  •  A & D to sprint  •  SPACE to lean', cx, cy + 28);
  }

  if (state === 'marks') {
    ctx.fillStyle = 'rgba(0,0,0,0.45)'; ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.font = 'bold 68px "Bebas Neue", "Arial Black", Impact, sans-serif';
    ctx.shadowColor = 'rgba(0,0,0,0.85)'; ctx.shadowBlur = 18; ctx.shadowOffsetX = 2; ctx.shadowOffsetY = 3;
    ctx.fillStyle = '#ffffff';
    ctx.fillText('On your marks', cx, cy);
    ctx.shadowColor = 'transparent'; ctx.shadowBlur = 0; ctx.shadowOffsetX = 0; ctx.shadowOffsetY = 0;
  }

  if (state === 'set') {
    ctx.fillStyle = 'rgba(0,0,0,0.45)'; ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.font = 'bold 84px "Bebas Neue", "Arial Black", Impact, sans-serif';
    ctx.shadowColor = 'rgba(0,0,0,0.85)'; ctx.shadowBlur = 18; ctx.shadowOffsetX = 2; ctx.shadowOffsetY = 3;
    ctx.fillStyle = '#ffffff';
    ctx.fillText('Set', cx, cy);
    ctx.shadowColor = 'transparent'; ctx.shadowBlur = 0; ctx.shadowOffsetX = 0; ctx.shadowOffsetY = 0;
  }

  if (state === 'gun') {
    const t = Math.max(0, 1 - (Date.now() - gunFiredAt) / 500);
    ctx.fillStyle = `rgba(0,0,0,${(0.72 * t).toFixed(3)})`;
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.globalAlpha = t;
    ctx.fillStyle = '#d95f2b';
    ctx.font = 'bold 160px monospace';
    ctx.fillText('GO!', cx, cy + 48);
    ctx.globalAlpha = 1;
  }

  if (state === 'false_start') {
    ctx.fillStyle = 'rgba(0,0,0,0.85)'; ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.fillStyle = '#e94560'; ctx.font = '130px "Bebas Neue", Impact, sans-serif';
    ctx.fillText('FALSE START', cx, cy - 30);
    ctx.fillStyle = '#ffffff'; ctx.font = '60px "Bebas Neue", Impact, sans-serif';
    ctx.fillText('DISQUALIFIED', cx, cy + 80);
    ctx.fillStyle = '#aaa'; ctx.font = 'bold 18px monospace';
    ctx.fillText('Press R to try again', cx, canvas.height - 48);
  }
}

// ── Drawing: finish overlay ───────────────────────────────────────────────────
function drawFinishOverlay() {
  if (!finishOrder.find(f => f.id === player.id)) {
    ctx.fillStyle = 'rgba(0,0,0,0.60)';
    ctx.beginPath(); ctx.roundRect(canvas.width/2-160, canvas.height/2-24, 320, 48, 8); ctx.fill();
    ctx.fillStyle='#fff'; ctx.font='bold 16px monospace'; ctx.textAlign='center'; ctx.fillText('RACE FINISHED', canvas.width/2, canvas.height/2-4);
    ctx.fillStyle='#aaa'; ctx.font='13px monospace'; ctx.fillText('Waiting for others...', canvas.width/2, canvas.height/2+16);
    return;
  }

  const playerTime = finishOrder.find(f => f.id === player.id).time;
  const pb      = getPB();
  const isNewPB = pb !== null && playerTime <= pb;
  const wrGapMs = playerTime - WR_MS;
  const posLabels = ['1st','2nd','3rd','4th'];
  const medals    = ['#ffd700','#c0c0c0','#cd7f32','#888'];
  const playerPos = finishOrder.findIndex(f => f.id === player.id);

  ctx.fillStyle = '#0f1923';
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const cy   = Math.round((canvas.height - 310) / 2);
  const col1X = 60;
  const col2X = Math.round(canvas.width / 2) + 40;

  // ── Left column ───────────────────────────────────────────────────────────
  ctx.textAlign = 'left';

  ctx.fillStyle = '#666'; ctx.font = 'bold 24px monospace';
  ctx.fillText('RACE FINISHED', col1X, cy + 14);

  ctx.fillStyle = '#fff'; ctx.font = 'bold 72px monospace';
  ctx.fillText(fmtTime(playerTime), col1X, cy + 90);

  ctx.fillStyle = medals[playerPos]; ctx.font = 'bold 24px monospace';
  ctx.fillText(posLabels[playerPos], col1X, cy + 122);
  if (isNewPB) {
    ctx.fillStyle = '#ffd700'; ctx.font = 'bold 14px monospace';
    ctx.fillText('★ NEW PB', col1X + 76, cy + 122);
  } else if (pb !== null) {
    ctx.fillStyle = '#777'; ctx.font = '16px monospace';
    ctx.fillText(`PB  ${fmtTime(pb)}`, col1X + 76, cy + 122);
  }

  const gapSign = wrGapMs >= 0 ? '+' : '−';
  const gapAbs  = Math.abs(wrGapMs);
  ctx.fillStyle = '#555'; ctx.font = '17px monospace';
  ctx.fillText(`${gapSign}${fmtTime(gapAbs)} from WR  (9.58s, Usain Bolt)`, col1X, cy + 148);

  ctx.strokeStyle = 'rgba(255,255,255,0.10)'; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(col1X, cy + 163); ctx.lineTo(col2X - 30, cy + 163); ctx.stroke();

  const rowBgColors = ['#4A3800', '#2A2A35', '#3A2000', '#202020'];
  finishOrder.forEach((f, i) => {
    const ry   = cy + 186 + i * 28;
    const font = f.ai ? '19px monospace' : 'bold 21px monospace';
    ctx.fillStyle = rowBgColors[i];
    ctx.fillRect(col1X - 8, ry - 18, col2X - 30 - (col1X - 8), 24);
    ctx.font = font;
    ctx.fillStyle = '#ffffff';
    ctx.fillText(`${posLabels[i]}  ${f.name.padEnd(6)}  ${fmtTime(f.time)}`, col1X, ry);
  });

  ctx.fillStyle = '#ccc'; ctx.font = '19px monospace';
  ctx.fillText('Press R to race again', col1X, cy + 310);

  // ── Right column: leaderboard ─────────────────────────────────────────────
  ctx.textAlign = 'left';

  ctx.fillStyle = '#888'; ctx.font = 'bold 14px monospace';
  ctx.fillText('ALL-TIME TOP 10', col2X, cy + 14);

  ctx.fillStyle = '#ffd700'; ctx.font = 'bold 16px monospace';
  ctx.fillText('★  Usain Bolt     9.58s  WR', col2X, cy + 42);

  ctx.strokeStyle = 'rgba(255,255,255,0.12)'; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(col2X, cy + 52); ctx.lineTo(canvas.width - 40, cy + 52); ctx.stroke();

  const nameColors = { YOU: '#4d96ff', Flash: '#ffd93d', Bolt: '#FF4DC4', Storm: '#6bcb77' };
  const lb = (cachedLB.length ? cachedLB : getLB()).map(normalizeLBEntry);
  lb.forEach((entry, i) => {
    const { ms: entryMs, name: entryName } = entry;
    const isThis = lbSaved && entryMs === playerTime && !lb.slice(0, i).some(e => e.ms === playerTime);
    const ry     = cy + 74 + i * 24;
    ctx.fillStyle = entryName ? (nameColors[entryName] || '#999') : '#999';
    ctx.font      = isThis ? 'bold 16px monospace' : '15px monospace';
    ctx.fillText(`${i + 1}. ${fmtTime(entryMs)}${entryName ? '  ' + entryName : ''}`, col2X, ry);
  });
}

// ── Drawing: starting blocks ─────────────────────────────────────────────────
function drawStartingBlocks() {
  const worldX = 60; // matches runner starting x
  for (let lane = 0; lane < 4; lane++) {
    const y  = laneY(lane);
    const gy = y + 74;              // runner ground level (matches drawRunner baseY)
    const sx = worldX - cameraX;
    if (sx < -80 || sx > canvas.width + 30) continue;

    ctx.fillStyle = '#2e2e2e';

    // Base rail — low bar connecting both plates at track level
    ctx.fillRect(sx - 7, gy - 2, 32, 4);

    // Front plate: larger, ~42° tilt. Bottom sits at track level.
    ctx.save();
    ctx.translate(sx + 14, gy - 7);
    ctx.rotate(-0.74);
    ctx.beginPath(); ctx.roundRect(-11, -3.5, 22, 7, 2); ctx.fill();
    ctx.restore();

    // Back plate: smaller, ~52° tilt. Also bottom at track level.
    ctx.save();
    ctx.translate(sx + 1, gy - 6);
    ctx.rotate(-0.91);
    ctx.beginPath(); ctx.roundRect(-8, -3, 16, 6, 2); ctx.fill();
    ctx.restore();
  }
}


// ── Drawing: title screen ─────────────────────────────────────────────────────
function drawTitleScreen() {
  const W = canvas.width, H = canvas.height;
  const cx = W / 2;

  ctx.fillStyle = '#0f1923';
  ctx.fillRect(0, 0, W, H);
  ctx.textAlign = 'center';

  ctx.fillStyle = '#ffffff';
  ctx.font = 'bold 108px monospace';
  ctx.fillText('SPRINT', cx, 220);

  ctx.fillStyle = '#d95f2b';
  ctx.font = 'bold 20px monospace';
  ctx.fillText('100M', cx, 268);

  ctx.strokeStyle = 'rgba(255,255,255,0.10)';
  ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(cx - 270, 300); ctx.lineTo(cx + 270, 300); ctx.stroke();

  ctx.fillStyle = 'rgba(255,255,255,0.28)';
  ctx.font = '11px monospace';
  ctx.fillText('C O N T R O L S', cx, 326);

  const rows = [
    ['CLICK', 'React to the starting gun'],
    ['A / D',  'Alternate to sprint'],
    ['SPACE',  'Lean at the finish line'],
    ['R',      'Restart at any time'],
  ];
  const badgeCx = cx - 165, badgeW = 90, badgeH = 27;
  const descX = cx - 107;

  rows.forEach(([key, desc], i) => {
    const y = 366 + i * 46;
    ctx.fillStyle = 'rgba(255,255,255,0.07)';
    ctx.beginPath(); ctx.roundRect(badgeCx - badgeW / 2, y - 18, badgeW, badgeH, 4); ctx.fill();
    ctx.strokeStyle = 'rgba(255,255,255,0.15)'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.roundRect(badgeCx - badgeW / 2, y - 18, badgeW, badgeH, 4); ctx.stroke();
    ctx.fillStyle = '#fff'; ctx.font = 'bold 13px monospace'; ctx.textAlign = 'center';
    ctx.fillText(key, badgeCx, y);
    ctx.fillStyle = 'rgba(255,255,255,0.55)'; ctx.font = '14px monospace'; ctx.textAlign = 'left';
    ctx.fillText(desc, descX, y);
  });

  const alpha = 0.65 + 0.35 * Math.sin(Date.now() / 700);
  ctx.globalAlpha = alpha;
  ctx.fillStyle = '#fff';
  ctx.font = 'bold 15px monospace';
  ctx.textAlign = 'center';
  ctx.fillText('CLICK ANYWHERE TO BEGIN', cx, H - 42);
  ctx.globalAlpha = 1;
}

// ── Main loop ─────────────────────────────────────────────────────────────────
function loop(timestamp = 0) {
  dt = lastTimestamp ? Math.min((timestamp - lastTimestamp) / (1000 / 60), 3) : 1;
  lastTimestamp = timestamp;

  ctx.clearRect(0, 0, canvas.width, canvas.height);

  if (state === 'title') {
    drawTitleScreen();
    requestAnimationFrame(loop);
    return;
  }

  if (['marks','set','gun'].includes(state)) updatePreRace();
  if (state === 'racing') update();

  if (state === 'finished') {
    runners.filter(r => r.ai && !finishOrder.find(f => f.id === r.id)).forEach(r => {
      const remainingMs = r.speed > 0 ? (TRACK_LENGTH - r.x) / r.speed * (1000 / 60) : 99999;
      finishOrder.push({ id: r.id, name: r.name, ai: r.ai, time: elapsedMs + remainingMs });
    });
    finishOrder.sort((a, b) => a.time - b.time);
    ctx.fillStyle = '#1a1a1a';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    drawFinishOverlay();
    return;
  }

  drawTrack();
  drawStartingBlocks();
  runners.forEach(drawRunner);

  if (state === 'racing') drawHUD();
  if (!['racing','finished'].includes(state)) drawPreRaceOverlay();

  requestAnimationFrame(loop);
}

requestAnimationFrame(loop);
