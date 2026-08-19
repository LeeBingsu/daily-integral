/*
 * make-icons.js - 앱·웹 아이콘(∫)을 다시 만든다.
 *
 *   실행: node make-icons.js          (Playwright + Chromium 이 있어야 한다)
 *
 *   글자를 가운데 정렬하면 브라우저는 '글자가 차지하는 칸'을 가운데 둔다.
 *   그런데 ∫ 는 그 칸 안에서 획이 한쪽으로 치우쳐 있는 글자라, 칸을 맞춰 봐야
 *   눈에 보이는 획은 가운데로 오지 않는다. 그래서 여기서는 획의 실제 경계를
 *   재서(actualBoundingBox) 그만큼 밀어 준다. 크기도 획의 높이를 기준으로
 *   맞추므로 글꼴이 바뀌어도 아이콘 안에서 차지하는 비율이 그대로다.
 */
var fs = require('fs');
var path = require('path');

var ROOT = __dirname;
var MIPMAP = path.join(ROOT, 'android/app/src/main/res');

var BG = '#eef2f7';
var GRID = 'rgba(23,42,69,.07)';
var INK = '#3b82c4';
var FONT = '"Times New Roman", Georgia, serif';

// 만들 것: [파일, 크기, 모양, 획이 차지할 높이 비율]
//   maskable 은 런처가 제멋대로 잘라내므로 안전 영역(가운데 80%) 안에 들어가게 작게 그린다.
var JOBS = [
  ['icons/icon-192.png', 192, 'rounded', 0.66],
  ['icons/icon-512.png', 512, 'rounded', 0.66],
  ['icons/maskable-512.png', 512, 'square', 0.50],
  ['icons/apple-touch-icon.png', 180, 'rounded', 0.66]
];

[['mdpi', 48], ['hdpi', 72], ['xhdpi', 96], ['xxhdpi', 144], ['xxxhdpi', 192]]
  .forEach(function (d) {
    JOBS.push(['android/app/src/main/res/mipmap-' + d[0] + '/ic_launcher.png', d[1], 'rounded', 0.66]);
    JOBS.push(['android/app/src/main/res/mipmap-' + d[0] + '/ic_launcher_round.png', d[1], 'circle', 0.62]);
  });

// 브라우저 안에서 도는 그리기 함수. 결과는 data URL 로 돌려준다.
function drawInPage(job) {
  var S = job.size, shape = job.shape, inkFrac = job.inkFrac;
  var BG = job.BG, GRID = job.GRID, INK = job.INK, FONT = job.FONT;
  var GLYPH = '∫';

  var cv = document.createElement('canvas');
  cv.width = S; cv.height = S;
  var ctx = cv.getContext('2d');

  // --- 바탕 -------------------------------------------------------
  ctx.save();
  ctx.beginPath();
  if (shape === 'circle') {
    ctx.arc(S / 2, S / 2, S / 2, 0, Math.PI * 2);
  } else if (shape === 'rounded') {
    var r = S * 0.22;
    ctx.moveTo(r, 0);
    ctx.arcTo(S, 0, S, S, r);
    ctx.arcTo(S, S, 0, S, r);
    ctx.arcTo(0, S, 0, 0, r);
    ctx.arcTo(0, 0, S, 0, r);
    ctx.closePath();
  } else {
    ctx.rect(0, 0, S, S);
  }
  ctx.clip();

  ctx.fillStyle = BG;
  ctx.fillRect(0, 0, S, S);

  // 사이트와 같은 모눈 바탕
  var g = S / 8;
  ctx.strokeStyle = GRID;
  ctx.lineWidth = Math.max(1, S / 256);
  for (var k = -4; k <= 4; k++) {
    var p = Math.round(S / 2 + k * g) + 0.5;
    ctx.beginPath(); ctx.moveTo(p, 0); ctx.lineTo(p, S); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(0, p); ctx.lineTo(S, p); ctx.stroke();
  }

  // --- 글자 -------------------------------------------------------
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';

  // 1차: 아무 크기로 재서 획의 실제 높이를 알아낸다
  var F0 = S;
  ctx.font = F0 + 'px ' + FONT;
  var m0 = ctx.measureText(GLYPH);
  var inkH0 = m0.actualBoundingBoxAscent + m0.actualBoundingBoxDescent;

  // 2차: 획 높이가 목표 비율이 되도록 글자 크기를 맞춘다
  var F = F0 * (inkFrac * S) / inkH0;
  ctx.font = F + 'px ' + FONT;
  var m = ctx.measureText(GLYPH);

  // textAlign/textBaseline 이 center/middle 이므로 그리는 자리를 원점으로 보면
  // 획은 좌 -actualBoundingBoxLeft ~ 우 +actualBoundingBoxRight 에 걸쳐 있다.
  // 그 한가운데가 아이콘 한가운데로 오도록 그리는 자리를 옮긴다.
  var inkCx = (m.actualBoundingBoxRight - m.actualBoundingBoxLeft) / 2;
  var inkCy = (m.actualBoundingBoxDescent - m.actualBoundingBoxAscent) / 2;

  ctx.fillStyle = INK;
  ctx.fillText(GLYPH, S / 2 - inkCx, S / 2 - inkCy);
  ctx.restore();

  // --- 검산: 실제로 칠해진 점의 경계를 세어 가운데인지 확인한다 ----
  var d = ctx.getImageData(0, 0, S, S).data;
  var x0 = S, x1 = -1, y0 = S, y1 = -1;
  for (var y = 0; y < S; y++) {
    for (var x = 0; x < S; x++) {
      var i = (y * S + x) * 4;
      // 바탕(연회색)과 획(파랑)을 파란 기운으로 가른다
      if (d[i + 3] > 40 && d[i + 2] - d[i] > 40) {
        if (x < x0) x0 = x; if (x > x1) x1 = x;
        if (y < y0) y0 = y; if (y > y1) y1 = y;
      }
    }
  }
  return {
    url: cv.toDataURL('image/png'),
    offX: +((x0 + x1) / 2 - S / 2).toFixed(2),   // 0 에 가까울수록 가운데
    offY: +((y0 + y1) / 2 - S / 2).toFixed(2),
    inkH: y1 - y0 + 1,
    inkW: x1 - x0 + 1
  };
}

(function () {
  var chromium;
  try {
    chromium = require('playwright').chromium;
  } catch (e) {
    console.error('Playwright 가 필요합니다: npm i -D playwright');
    process.exit(1);
  }

  chromium.launch({ executablePath: process.env.CHROME_PATH || undefined })
    .then(function (browser) {
      return browser.newPage().then(function (page) {
        return page.setContent('<!doctype html><meta charset=utf-8><body>')
          .then(function () {
            var chain = Promise.resolve();
            var bad = 0;

            JOBS.forEach(function (j) {
              chain = chain.then(function () {
                return page.evaluate(drawInPage, {
                  size: j[1], shape: j[2], inkFrac: j[3],
                  BG: BG, GRID: GRID, INK: INK, FONT: FONT
                });
              }).then(function (res) {
                var out = path.join(ROOT, j[0]);
                fs.mkdirSync(path.dirname(out), { recursive: true });
                fs.writeFileSync(out, Buffer.from(res.url.split(',')[1], 'base64'));

                // 획 끝이 가늘게 사라지는 글자라 경계를 재는 데 한두 점의 오차가 남는다.
                // 크기의 0.5% 안쪽이면 눈으로는 구분되지 않는다.
                var tol = Math.max(1, j[1] * 0.005);
                var ok = Math.abs(res.offX) <= tol && Math.abs(res.offY) <= tol;
                if (!ok) bad++;
                console.log(
                  (ok ? '  ' : '!!') + ' ' + j[0] +
                  '  ' + j[1] + 'px  획 ' + res.inkW + '×' + res.inkH +
                  '  중심에서 ' + res.offX + ', ' + res.offY);
              });
            });

            return chain.then(function () {
              return browser.close().then(function () {
                if (bad) {
                  console.error('가운데에서 벗어난 아이콘이 ' + bad + '개 있습니다.');
                  process.exit(1);
                }
                console.log('아이콘 ' + JOBS.length + '개 생성 완료');
              });
            });
          });
      });
    })
    .catch(function (e) { console.error(e); process.exit(1); });
})();
