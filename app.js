/* app.js - 화면 로직. 상태는 localStorage 에만 저장한다. */
(function () {
  'use strict';

  var STORE_KEY = 'dailyIntegral.local.v1';
  var $ = function (id) { return document.getElementById(id); };

  // 안드로이드 앱(APK)은 내가 직접 깔아서 쓰는 것이라 관리자 키를 묻지 않는다.
  // 웹은 주소만 알면 누구나 들어오므로 잠금을 그대로 둔다.
  var IS_APP = location.hostname === 'appassets.androidplatform.net';

  function isAdmin() { return IS_APP || store.admin; }

  // 터치 기기(휴대폰·태블릿)에서는 입력칸에 자동 포커스를 주지 않는다.
  // 포커스를 주면 문제를 열자마자 화면 절반을 가리며 키보드가 올라온다.
  function isTouch() {
    return !!(window.matchMedia && window.matchMedia('(hover: none) and (pointer: coarse)').matches);
  }

  // ------------------------------------------------------------- 저장소

  function blankStore() {
    return {
      theme: 'light',
      streak: 0,
      best: 0,
      lastSolvedDay: null,
      days: {},                       // '2026-08-18': { easy: {solved, attempts, hints, revealed} }
      // open: 꺼내 두고 아직 끝내지 않은 연습 문제 (난이도 -> 문제 id)
      practice: { solved: 0, attempts: 0, day: null, used: {}, open: {} },
      // penOnly 가 null 이면 '자동' — 터치가 되는 기기에서만 켠다
      pad: { penOnly: null, color: 0, width: 1 },
      admin: false
    };
  }

  var store = load();

  function load() {
    try {
      var raw = localStorage.getItem(STORE_KEY);
      if (!raw) return blankStore();
      var s = JSON.parse(raw);
      var base = blankStore();
      Object.keys(base).forEach(function (k) { if (s[k] === undefined) s[k] = base[k]; });
      Object.keys(base.practice).forEach(function (k) {
        if (s.practice[k] === undefined) s.practice[k] = base.practice[k];
      });
      Object.keys(base.pad).forEach(function (k) {
        if (s.pad[k] === undefined) s.pad[k] = base.pad[k];
      });
      return s;
    } catch (e) { return blankStore(); }
  }

  function save() {
    try { localStorage.setItem(STORE_KEY, JSON.stringify(store)); } catch (e) { /* 시크릿 모드 등 */ }
  }

  // ------------------------------------------------------------- 날짜

  function keyOf(d) {
    var m = String(d.getMonth() + 1).padStart(2, '0');
    var day = String(d.getDate()).padStart(2, '0');
    return d.getFullYear() + '-' + m + '-' + day;
  }

  function dayNumberOf(d) {
    return Math.floor(Date.UTC(d.getFullYear(), d.getMonth(), d.getDate()) / 86400000);
  }

  function dateFromKey(k) {
    var p = k.split('-');
    return new Date(+p[0], +p[1] - 1, +p[2]);
  }

  function prettyDate(k) {
    var d = dateFromKey(k);
    var w = ['일', '월', '화', '수', '목', '금', '토'][d.getDay()];
    return (d.getMonth() + 1) + '월 ' + d.getDate() + '일 (' + w + ')';
  }

  var TODAY_KEY = keyOf(new Date());

  // ------------------------------------------------------------- 문제 선택

  function mulberry32(a) {
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function shuffledIndices(n, seed) {
    var rnd = mulberry32(seed);
    var arr = [];
    for (var i = 0; i < n; i++) arr.push(i);
    for (var j = n - 1; j > 0; j--) {
      var k = Math.floor(rnd() * (j + 1));
      var t = arr[j]; arr[j] = arr[k]; arr[k] = t;
    }
    return arr;
  }

  // 같은 주기 안에서는 문제가 반복되지 않도록 순열에서 뽑는다.
  function problemForDay(level, dayNum) {
    var bank = PROBLEMS.byLevel[level];
    var n = bank.length;
    var cycle = Math.floor(dayNum / n);
    var pos = ((dayNum % n) + n) % n;
    var levelSeed = PROBLEMS.levels.indexOf(level) * 7919;
    var order = shuffledIndices(n, cycle * 1000003 + levelSeed + 4242);
    return bank[order[pos]];
  }

  function randomProblem(level, avoidId) {
    var bank = PROBLEMS.byLevel[level];
    var p, guard = 0;
    do { p = bank[Math.floor(Math.random() * bank.length)]; } while (p.id === avoidId && ++guard < 20);
    return p;
  }

  // ------------------------------------------------------------- 연습 모드 하루 몫

  // 무한 연습이 정말 무한해지지 않도록 난이도별로 하루 배당을 둔다.
  // Infinity 는 저장하지 않고 상수로만 쓰므로 JSON 직렬화에 걸리지 않는다.
  var PRACTICE_QUOTA = { easy: Infinity, medium: 3, hard: 7, monster: 1 };

  // 관리자 키의 해시(FNV-1a). 소스에 키를 그대로 적어두지 않으려는 것뿐이고,
  // 브라우저 콘솔로 store 를 고치면 뚫린다 — 자기 절제용 장치이지 접근 통제가 아니다.
  var ADMIN_HASH = '4cde032d';

  function fnv1a(str) {
    var h = 0x811c9dc5;
    for (var i = 0; i < str.length; i++) {
      h ^= str.charCodeAt(i);
      h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
    }
    return h.toString(16);
  }

  // 날짜가 바뀌면 사용량을 턴다
  function rollPracticeDay() {
    if (store.practice.day === TODAY_KEY) return;
    store.practice.day = TODAY_KEY;
    store.practice.used = {};
    save();
  }

  function practiceUsed(level) {
    rollPracticeDay();
    return store.practice.used[level] || 0;
  }

  function practiceLeft(level) {
    if (isAdmin()) return Infinity;
    var q = PRACTICE_QUOTA[level];
    if (q === Infinity) return Infinity;
    return Math.max(0, q - practiceUsed(level));
  }

  // 문제 id 로 찾아보기 (연습하다 만 문제를 다시 꺼낼 때 쓴다)
  var problemById = null;

  function findProblem(id) {
    if (!id) return null;
    if (!problemById) {
      problemById = {};
      PROBLEMS.all.forEach(function (p) { problemById[p.id] = p; });
    }
    return problemById[id] || null;
  }

  function consumePractice(level) {
    if (isAdmin() || PRACTICE_QUOTA[level] === Infinity) return;
    store.practice.used[level] = practiceUsed(level) + 1;
    save();
  }

  /*
   * 연습 문제 한 개를 꺼낸다. 몫이 없으면 자물쇠 화면을 띄운다.
   *
   *   한 번 꺼낸 문제는 끝낼 때까지 난이도별로 들고 있는다. 난이도를 바꿨다
   *   돌아오거나 첫 화면에 다녀와도 풀던 문제가 그대로 있고, 하루 몫도 그대로다.
   *   몫은 '새 문제를 꺼낼 때'만 깎인다 — fresh 를 주면(다음 문제 버튼) 새로 꺼낸다.
   */
  function startPractice(level, avoidId, fresh) {
    session.mode = 'practice';
    session.level = level;

    if (!fresh) {
      var open = findProblem(store.practice.open[level]);
      if (open) {
        showLock(null);
        loadProblem(open);
        renderQuota();
        renderLevels();
        return true;
      }
    }

    if (practiceLeft(level) <= 0) {
      showLock(level);
      renderLevels();
      renderQuota();
      return false;
    }

    consumePractice(level);
    var p = randomProblem(level, avoidId);
    store.practice.open[level] = p.id;
    save();
    showLock(null);
    loadProblem(p);
    renderQuota();
    renderLevels();
    return true;
  }

  function showLock(level) {
    var locked = !!level;
    $('lockCard').classList.toggle('hidden', !locked);
    $('playCard').classList.toggle('hidden', locked);
    $('rulesCard').classList.toggle('hidden', locked);
    if (!locked) return;
    buildGrass();
    var q = PRACTICE_QUOTA[level];
    $('lockMsg').innerHTML = '<b>' + PROBLEMS.labels[level] + '</b> 연습은 하루 ' + q +
      '문제까지입니다. 오늘 몫을 다 썼어요.';
    $('lockSub').textContent = '자정에 다시 채워집니다. 다른 난이도를 고르거나, ' +
      '오늘의 문제를 풀어 보세요.';
  }

  // ------------------------------------------------------------- Touch Grass

  // 잔디밭은 SVG 로 직접 그린다. 직접 찍었거나 사용 허락을 받은 사진이 있으면
  // 파일을 넣고 아래 경로만 채우면 그 사진이 대신 깔린다. 비워 두면 SVG 를 쓴다.
  var GRASS_PHOTO = '';

  var grassDrawn = false;

  function buildGrass() {
    if (grassDrawn) return;
    grassDrawn = true;

    if (GRASS_PHOTO) {
      var art = $('grassArt');
      var img = document.createElement('img');
      img.className = 'grass-photo';
      img.alt = '';
      img.onerror = function () { img.remove(); };
      img.src = GRASS_PHOTO;
      art.insertBefore(img, art.firstChild);
    }

    var NS = 'http://www.w3.org/2000/svg';
    var svg = $('grassSvg');
    var W = 600, H = 260;

    // 씨앗 고정 난수 — 볼 때마다 잔디가 달라지지 않게 한다
    var seed = 20260819;
    function rnd() {
      seed = (seed * 1103515245 + 12345) & 0x7fffffff;
      return seed / 0x7fffffff;
    }

    var defs = document.createElementNS(NS, 'defs');
    defs.innerHTML =
      '<linearGradient id="grassSky" x1="0" y1="0" x2="0" y2="1">' +
        '<stop offset="0" stop-color="#cfe89a"/><stop offset="1" stop-color="#5aa03a"/>' +
      '</linearGradient>' +
      '<radialGradient id="grassSun" cx="0.82" cy="0.12" r="0.75">' +
        '<stop offset="0" stop-color="#fff8c8" stop-opacity=".85"/>' +
        '<stop offset="1" stop-color="#fff8c8" stop-opacity="0"/>' +
      '</radialGradient>';
    svg.appendChild(defs);

    var bg = document.createElementNS(NS, 'rect');
    bg.setAttribute('width', W); bg.setAttribute('height', H);
    bg.setAttribute('fill', 'url(#grassSky)');
    svg.appendChild(bg);

    // 아래쪽은 빽빽한 뗏장으로 깔아 밑동이 비지 않게 한다
    var turf = document.createElementNS(NS, 'rect');
    turf.setAttribute('y', H - 70); turf.setAttribute('width', W); turf.setAttribute('height', 70);
    turf.setAttribute('fill', '#4b8a2e'); turf.setAttribute('opacity', '.55');
    svg.appendChild(turf);

    // 뒤에서 앞으로 네 겹 — 뒤는 흐리고 짧게, 앞은 진하고 길게
    [[240, 40, 88, 1.7, .5], [230, 70, 130, 2.4, .72], [210, 105, 180, 3.2, .9],
     [150, 150, 245, 4.4, 1]]
      .forEach(function (layer) {
        var n = layer[0], hMin = layer[1], hMax = layer[2], wMax = layer[3], op = layer[4];
        for (var i = 0; i < n; i++) {
          var x = rnd() * (W + 40) - 20;
          var h = hMin + rnd() * (hMax - hMin);
          var lean = (rnd() - 0.5) * h * 0.55;
          var w = 1.1 + rnd() * wMax;
          var hue = 74 + rnd() * 34;
          var light = 24 + rnd() * 26 + (1 - op) * 14;
          var d = 'M' + x.toFixed(1) + ',' + H +
                  ' Q' + (x + lean * 0.3).toFixed(1) + ',' + (H - h * 0.58).toFixed(1) +
                  ' ' + (x + lean).toFixed(1) + ',' + (H - h).toFixed(1);
          var p = document.createElementNS(NS, 'path');
          p.setAttribute('d', d);
          p.setAttribute('stroke', 'hsl(' + hue.toFixed(0) + ',' + (44 + rnd() * 26).toFixed(0) +
                         '%,' + light.toFixed(0) + '%)');
          p.setAttribute('stroke-width', w.toFixed(2));
          p.setAttribute('stroke-linecap', 'round');
          p.setAttribute('fill', 'none');
          p.setAttribute('opacity', op.toFixed(2));
          svg.appendChild(p);
        }
      });

    var sun = document.createElementNS(NS, 'rect');
    sun.setAttribute('width', W); sun.setAttribute('height', H);
    sun.setAttribute('fill', 'url(#grassSun)');
    svg.appendChild(sun);
  }

  function renderQuota() {
    var bar = $('quotaBar');
    bar.classList.toggle('hidden', session.mode !== 'practice');
    if (session.mode !== 'practice') return;
    bar.innerHTML = '';

    var info = document.createElement('span');
    info.className = 'quota-info';
    if (isAdmin()) {
      info.innerHTML = IS_APP
        ? '앱 · 하루 제한 없음'
        : '<b>관리자</b> · 하루 제한 없음';
    } else {
      info.innerHTML = PROBLEMS.levels.map(function (lv) {
        var q = PRACTICE_QUOTA[lv];
        if (q === Infinity) return PROBLEMS.labels[lv] + ' <b>\u221e</b>';
        return PROBLEMS.labels[lv] + ' <b>' + practiceLeft(lv) + '</b>/' + q;
      }).join('<i>\u00b7</i>');
    }
    bar.appendChild(info);
  }

  // onSuccess 를 주면 통과 뒤 그것만 실행한다 (아카이브에서 눌렀을 때 등)
  function askAdminKey(onSuccess) {
    var v = window.prompt('관리자 키를 입력하면 연습 하루 제한과 아카이브 잠금이 풀립니다.');
    if (v === null) return;
    if (fnv1a(v.trim()) !== ADMIN_HASH) {
      window.alert('관리자 키가 맞지 않습니다.');
      return;
    }
    store.admin = true;
    save();
    renderQuota();
    renderLevels();
    renderArchive();
    renderAdminBtn();
    if (onSuccess) { onSuccess(); return; }
    if ($('lockCard').classList.contains('hidden')) {
      showFeedback('ok', '관리자 모드입니다. 하루 제한이 풀렸습니다.');
    } else {
      startPractice(session.level, session.problem && session.problem.id);
    }
  }

  // 관리자 키는 맨 아래 한 자리에만 둔다. 앱에서는 아예 안 쓰므로 감춘다.
  function renderAdminBtn() {
    var b = $('adminBtn');
    b.classList.toggle('hidden', IS_APP);
    b.textContent = store.admin ? '관리자 잠그기' : '관리자 키';
  }

  function lockAdmin() {
    store.admin = false;
    save();
    renderQuota();
    renderLevels();
    renderArchive();
    renderAdminBtn();
    if (practiceLeft(session.level) <= 0) showLock(session.level);
  }

  // ------------------------------------------------------------- 수식 렌더

  function renderTex(el, tex, display, fallbackText) {
    if (window.katex) {
      try {
        katex.render(tex, el, { displayMode: !!display, throwOnError: false });
        return;
      } catch (e) { /* 아래 폴백 */ }
    }
    el.innerHTML = '';
    var span = document.createElement('span');
    span.className = 'fallback';
    span.textContent = fallbackText || tex;
    el.appendChild(span);
  }

  // '$수식$' 과 한글 설명이 섞인 문자열을 렌더링한다.
  function renderMixed(el, str, big) {
    el.innerHTML = '';
    var parts = String(str).split('$');
    parts.forEach(function (part, i) {
      if (part === '') return;
      if (i % 2 === 1) {
        var span = document.createElement('span');
        renderTex(span, (big ? '\\displaystyle ' : '') + part, false, part);
        el.appendChild(span);
      } else {
        el.appendChild(document.createTextNode(part));
      }
    });
  }

  // ------------------------------------------------------------- 세션 상태

  var session = {
    mode: 'daily',        // daily | practice | archive
    dateKey: TODAY_KEY,
    level: 'easy',
    problem: null,
    attempts: 0,
    hintsShown: 0,
    solved: false,
    revealed: false
  };

  function recordFor(dateKey, level) {
    var d = store.days[dateKey];
    return d ? d[level] : null;
  }

  function ensureRecord(dateKey, level) {
    if (!store.days[dateKey]) store.days[dateKey] = {};
    if (!store.days[dateKey][level]) {
      store.days[dateKey][level] = { solved: false, attempts: 0, hints: 0, revealed: false };
    }
    return store.days[dateKey][level];
  }

  function effectiveStreak() {
    if (!store.lastSolvedDay) return 0;
    var last = dayNumberOf(dateFromKey(store.lastSolvedDay));
    var today = dayNumberOf(new Date());
    return (today - last <= 1) ? store.streak : 0;
  }

  function markSolved() {
    if (session.mode === 'practice') {
      store.practice.solved++;
      save();
      return;
    }
    var rec = ensureRecord(session.dateKey, session.level);
    rec.solved = true;
    rec.attempts = session.attempts;
    rec.hints = session.hintsShown;
    rec.revealed = session.revealed;

    // 연속 학습일은 "오늘의 문제"를 풀었을 때만 갱신된다.
    if (session.dateKey === TODAY_KEY && store.lastSolvedDay !== TODAY_KEY) {
      var yesterday = keyOf(new Date(Date.now() - 86400000));
      store.streak = (store.lastSolvedDay === yesterday) ? store.streak + 1 : 1;
      store.lastSolvedDay = TODAY_KEY;
      if (store.streak > store.best) store.best = store.streak;
    }
    save();
  }

  function bumpAttempt() {
    session.attempts++;
    if (session.mode === 'practice') { store.practice.attempts++; }
    else { ensureRecord(session.dateKey, session.level).attempts = session.attempts; }
    save();
  }

  // ------------------------------------------------------------- 화면 그리기

  function loadProblem(problem) {
    session.problem = problem;
    session.attempts = 0;
    session.hintsShown = 0;
    session.solved = false;
    session.revealed = false;

    var rec = session.mode === 'practice' ? null : recordFor(session.dateKey, session.level);
    if (rec) {
      session.attempts = rec.attempts || 0;
      session.solved = !!rec.solved;
      session.revealed = !!rec.revealed;
      session.hintsShown = rec.hints || 0;
    }

    $('dateChip').textContent = session.mode === 'practice'
      ? '연습 · ' + PROBLEMS.labels[session.level]
      : prettyDate(session.dateKey);

    var modeChip = $('modeChip');
    if (session.mode === 'archive') {
      modeChip.textContent = '아카이브';
      modeChip.classList.remove('hidden');
    } else if (session.mode === 'practice') {
      modeChip.textContent = '무한 연습';
      modeChip.classList.remove('hidden');
    } else {
      modeChip.classList.add('hidden');
    }

    var isDef = problem.value !== undefined;
    var bounds = isDef ? '_{' + problem.loLatex + '}^{' + problem.hiLatex + '}' : '';
    renderTex($('problemBox'), '\\int' + bounds + ' ' + problem.latex + '\\,dx', true,
      '∫ ' + problem.integrand + ' dx');

    // 정적분은 답이 상수라 입력 안내와 팔레트가 달라진다
    $('answerInput').placeholder = isDef
      ? '예:  pi^2/6     (x 없는 상수로 답하세요)'
      : '예:  x³/3 + C     (적분상수는 생략해도 됩니다)';
    $('palette').classList.toggle('def', isDef);

    // 연습장은 문제마다 따로 남는다
    padSyncProblem();

    $('nextBtn').classList.toggle('hidden', session.mode !== 'practice');
    $('answerInput').value = '';
    $('hintBox').innerHTML = '';
    $('solution').classList.remove('show');
    $('feedback').className = 'feedback';
    updatePreview();
    updateAttemptChip();
    renderLevels();

    if (session.solved) {
      showFeedback('ok', '이미 해결한 문제입니다. 다시 풀어 보거나 해설을 확인해 보세요.');
    }
    if (session.revealed) revealSolution(true);

    for (var i = 0; i < session.hintsShown; i++) appendHint(i);
    if (!isTouch()) $('answerInput').focus();
  }

  function updateAttemptChip() {
    var bits = [];
    if (session.attempts) bits.push('시도 ' + session.attempts + '회');
    if (session.hintsShown) bits.push('힌트 ' + session.hintsShown + '개');
    if (session.solved) bits.push('해결 ✓');
    $('attemptChip').textContent = bits.join(' · ');
  }

  function showFeedback(kind, html) {
    var el = $('feedback');
    el.className = 'feedback show ' + kind;
    el.innerHTML = html;
  }

  function appendHint(i) {
    var p = session.problem;
    if (!p.hints[i]) return;
    var box = document.createElement('div');
    box.className = 'hint';
    var n = document.createElement('span');
    n.className = 'n';
    n.textContent = '힌트 ' + (i + 1);
    var body = document.createElement('span');
    renderMixed(body, p.hints[i], true);
    box.appendChild(n);
    box.appendChild(body);
    $('hintBox').appendChild(box);
  }

  function revealSolution(silent) {
    var p = session.problem;
    var steps = $('steps');
    steps.innerHTML = '';
    p.steps.forEach(function (s) {
      var row = document.createElement('div');
      row.className = 'step';
      var body = document.createElement('span');
      renderMixed(body, s, true);
      row.appendChild(body);
      steps.appendChild(row);
    });
    if (p.value !== undefined) renderTex($('finalAnswer'), p.valueLatex, false, '= ' + p.value);
    else renderTex($('finalAnswer'), p.answerLatex, false, p.answer + ' + C');
    $('solution').classList.add('show');
    session.revealed = true;
    if (session.mode !== 'practice') {
      ensureRecord(session.dateKey, session.level).revealed = true;
      save();
    } else if (store.practice.open[session.level] === p.id) {
      // 다 끝낸 문제는 놓아준다. '다음 문제'는 새로 꺼내고 그때 몫이 깎인다.
      delete store.practice.open[session.level];
      save();
    }
    if (!silent) updateAttemptChip();
  }

  // ------------------------------------------------------------- 채점

  function check() {
    var raw = $('answerInput').value.trim();
    if (!raw) { showFeedback('info', '답을 입력해 주세요.'); return; }
    var p = session.problem;

    var res;
    try {
      res = p.value !== undefined
        ? MathExpr.compareValue(raw, p.value)
        : MathExpr.compareAntiderivative(raw, p.answer, p.domain, p.integrand);
    } catch (e) {
      showFeedback('bad', '수식을 읽을 수 없습니다: ' + e.message);
      return;
    }

    if (res.ok) {
      var wasSolved = session.solved;
      session.solved = true;
      if (!wasSolved) markSolved();
      var extra = session.revealed ? ' (해설을 본 뒤 정답)' : '';
      showFeedback('ok', '<b>정답입니다.</b> ' +
        (session.attempts === 0 ? '한 번에 맞혔습니다' : session.attempts + '번의 시도 끝에 맞혔습니다') + extra + '.');
      revealSolution(true);
      updateAttemptChip();
      renderLevels();
      renderStreak();
      renderArchive();
      renderStats();
      return;
    }

    bumpAttempt();
    updateAttemptChip();

    if (res.reason === 'parse') {
      showFeedback('bad', '수식 해석 실패: ' + res.detail);
    } else if (res.reason === 'novar') {
      showFeedback('bad', res.detail + ' 부정적분은 x 의 함수여야 합니다.');
    } else if (res.reason === 'hasvar' || res.reason === 'hasfree' || res.reason === 'nan') {
      showFeedback('bad', res.detail);
    } else if (res.reason === 'domain') {
      showFeedback('bad', res.detail);
    } else if (p.value !== undefined) {
      showFeedback('bad', '<b>오답입니다.</b> 값이 맞지 않습니다.');
    } else {
      showFeedback('bad', '<b>오답입니다.</b> ' + (res.detail || '미분해서 피적분함수가 되는지 확인해 보세요.'));
    }
  }

  // ------------------------------------------------------------- 예쁜 입력

  // 타이핑하는 대로 * 는 ·, ^2 는 ², sqrt 는 √, pi 는 π 로 바꿔 보여 준다.
  // 파서가 이 기호들을 그대로 읽으므로 채점에는 영향이 없다.
  var SUP = {
    '0': '\u2070', '1': '\u00b9', '2': '\u00b2', '3': '\u00b3', '4': '\u2074',
    '5': '\u2075', '6': '\u2076', '7': '\u2077', '8': '\u2078', '9': '\u2079',
    '-': '\u207b', '+': '\u207a', 'x': '\u02e3', 'n': '\u207f'
  };
  var SUP_DIGITS = '\u2070\u00b9\u00b2\u00b3\u2074\u2075\u2076\u2077\u2078\u2079\u207b';
  // 괄호로 묶인 지수 안에서 위첨자로 바꿀 수 있는 글자
  var SUP_GROUP_RE = /^[0-9+\-xn]+$/;

  function ends(str, tail) {
    return str.length >= tail.length && str.slice(str.length - tail.length) === tail;
  }

  // 방금 입력한 자리만 살펴본다. 커서가 튀지 않도록 앞쪽 문자열만 손댄다.
  function prettifyAtCaret(value, caret) {
    var before = value.slice(0, caret), after = value.slice(caret);
    var last = before.slice(-1);
    var cut = 0, put = null;

    if (last === '*') { cut = 1; put = '\u00b7'; }
    else if (ends(before, 'sqrt(')) { cut = 5; put = '\u221a('; }
    else if (ends(before, 'pi') && !/[A-Za-z]/.test(before.slice(-3, -2))) { cut = 2; put = '\u03c0'; }
    else if (last === ')') { return closeExponentGroup(before, after); }
    else if (/\^[0-9\-xn]$/.test(before)) { cut = 2; put = SUP[last]; }
    else if (/[0-9]$/.test(before)) {
      // 위첨자 바로 뒤에 이어 친 숫자만 위첨자로 (x^12 -> x¹²)
      var prev = before.slice(-2, -1);
      if (prev && SUP_DIGITS.indexOf(prev) >= 0) { cut = 1; put = SUP[last]; }
    }

    if (put === null) return null;
    before = before.slice(0, before.length - cut) + put;
    return { value: before + after, caret: before.length };
  }

  // 방금 닫은 괄호가 지수 괄호 ^( ... ) 라면 통째로 위첨자로 바꾼다.
  // 괄호가 범위를 확정해 주므로 e^(2x) -> e²ˣ 가 모호하지 않다.
  function closeExponentGroup(before, after) {
    var close = before.length - 1;               // 방금 친 ')' 의 위치
    var depth = 1, open = -1;
    for (var i = close - 1; i >= 0; i--) {
      if (before[i] === ')') depth++;
      else if (before[i] === '(') { depth--; if (depth === 0) { open = i; break; } }
    }
    if (open < 1 || before[open - 1] !== '^') return null;

    var inner = before.slice(open + 1, close);
    if (!inner || !SUP_GROUP_RE.test(inner)) return null;   // 1/2, x^2 등은 그대로 둔다

    var sup = '';
    for (var j = 0; j < inner.length; j++) sup += SUP[inner[j]];
    var head = before.slice(0, open - 1) + sup;             // '^' 와 괄호는 지운다
    return { value: head + after, caret: head.length };
  }

  function toSup(_, chars) {
    var out = '';
    for (var i = 0; i < chars.length; i++) out += SUP[chars[i]];
    return out;
  }

  // 붙여넣기처럼 한꺼번에 들어온 값은 전체를 훑어서 바꾼다.
  function prettifyAll(value) {
    return value
      .replace(/sqrt\s*\(/g, '\u221a(')
      .replace(/(^|[^A-Za-z])pi(?![A-Za-z])/g, '$1\u03c0')
      .replace(/\*/g, '\u00b7')
      .replace(/\^\(([0-9+\-xn]+)\)/g, toSup)      // e^(2x) -> e²ˣ
      .replace(/\^(-?[0-9]+)(?![0-9])/g, toSup)
      .replace(/\^([xn])(?![A-Za-z0-9])/g, toSup);
  }

  function onAnswerInput(e) {
    var inp = $('answerInput');
    if (e && e.inputType === 'insertFromPaste') {
      inp.value = prettifyAll(inp.value);
      inp.setSelectionRange(inp.value.length, inp.value.length);
    } else if (!e || e.inputType !== 'deleteContentBackward') {
      var res = prettifyAtCaret(inp.value, inp.selectionStart);
      if (res) {
        inp.value = res.value;
        inp.setSelectionRange(res.caret, res.caret);
      }
    }
    updatePreview();
  }

  // ------------------------------------------------------------- 미리보기

  function updatePreview() {
    var raw = $('answerInput').value.trim();
    var body = $('previewBody');
    var box = $('preview');
    box.classList.remove('err');
    if (!raw) {
      box.classList.add('empty');
      body.className = 'muted';
      body.textContent = '입력한 식이 여기에 수식으로 표시됩니다';
      return;
    }
    box.classList.remove('empty');
    body.className = '';
    try {
      var tex = MathExpr.latexOf(raw);
      renderTex(body, '\\displaystyle ' + tex, false, raw);
    } catch (e) {
      box.classList.add('err');
      body.textContent = e.message;
    }
  }

  // ------------------------------------------------------------- 구슬 허브

  // 가운데 표제를 중심으로 구슬을 원형으로 돌려 배치한다.
  // 각도는 CSS 변수로 넘기고, 배치는 transform 이 맡는다.
  var ORBS = [
    { key: 'easy',     glyph: 'E', label: '쉬움',   color: 'var(--lv-easy)' },
    { key: 'medium',   glyph: 'M', label: '보통',   color: 'var(--lv-medium)' },
    { key: 'hard',     glyph: 'H', label: '어려움', color: 'var(--lv-hard)' },
    { key: 'monster',  glyph: 'X', label: '몬스터', color: 'var(--lv-monster)' },
    { key: 'practice', glyph: '\u221e', label: '연습',   color: 'var(--lv-practice)' },
    { key: 'archive',  glyph: 'A', label: '아카이브', color: 'var(--lv-archive)' },
    { key: 'stats',    glyph: 'S', label: '통계',   color: 'var(--lv-stats)' }
  ];

  var WEB_R = 36.5;   // viewBox(100×100) 기준 반지름 — CSS 의 --r 비율과 맞춰 둔 값
  var TURN_MS = 620;  // styles.css 의 --turn 과 같은 값

  var orbEls = [];        // 구슬 버튼
  var spinEls = [];       // 구슬 안쪽 회전 보정 래퍼
  var ringAngle = 0;      // 고리의 누적 회전각(도). 360 을 넘어도 되감지 않는다
  var topIndex = 0;

  function reducedMotion() {
    return !!(window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches);
  }

  // 고리를 돌려 i 번 구슬을 맨 위로 올린다. 항상 가까운 쪽으로 돈다.
  function spinToTop(i, done) {
    var target = -360 * i / ORBS.length;
    var delta = ((target - ringAngle) % 360 + 540) % 360 - 180;
    ringAngle += delta;

    $('hubRing').style.transform = 'rotate(' + ringAngle + 'deg)';
    spinEls.forEach(function (el) { el.style.transform = 'rotate(' + (-ringAngle) + 'deg)'; });

    orbEls.forEach(function (el, k) { el.classList.toggle('top', k === i); });
    topIndex = i;

    if (!done) return;
    var moving = Math.abs(delta) > 0.5 && !reducedMotion();
    if (moving) setTimeout(done, TURN_MS);
    else done();
  }

  function renderHub() {
    var ring = $('hubRing');
    ring.querySelectorAll('.orb').forEach(function (n) { n.remove(); });
    orbEls = []; spinEls = [];

    var n = ORBS.length, pts = [];
    ORBS.forEach(function (o, i) {
      var deg = -90 + 360 * i / n;
      var rad = deg * Math.PI / 180;
      pts.push([50 + WEB_R * Math.cos(rad), 50 + WEB_R * Math.sin(rad)]);

      var b = document.createElement('button');
      b.className = 'orb';
      b.style.setProperty('--a', deg + 'deg');
      b.style.setProperty('--c', o.color);
      b.setAttribute('aria-label', o.label);

      var spin = document.createElement('span');
      spin.className = 'spin';
      b.appendChild(spin);

      var ball = document.createElement('span');
      ball.className = 'ball';
      ball.textContent = o.glyph;
      spin.appendChild(ball);

      var lab = document.createElement('span');
      lab.className = 'lab';
      lab.textContent = o.label;
      spin.appendChild(lab);

      var rec = PROBLEMS.labels[o.key] ? recordFor(TODAY_KEY, o.key) : null;
      if (rec && rec.solved) {
        var t = document.createElement('span');
        t.className = 'tick';
        t.textContent = '\u2713';
        spin.appendChild(t);
      }

      b.onclick = function () {
        spinToTop(i, function () {
          if (o.key === 'practice' || o.key === 'archive' || o.key === 'stats') {
            switchView(o.key);
          } else {
            session.level = o.key;
            switchView('daily');
          }
        });
      };
      orbEls.push(b);
      spinEls.push(spin);
      ring.appendChild(b);
    });

    drawWeb(pts);

    // 다시 그려도 직전 회전 상태를 그대로 이어받는다 — 이때는 굴러가지 않게 한다
    var frozen = [ring].concat(spinEls);
    frozen.forEach(function (el) { el.style.transition = 'none'; });
    spinToTop(topIndex);
    void ring.offsetWidth;
    frozen.forEach(function (el) { el.style.transition = ''; });
  }

  // 구슬 사이를 잇는 점선 — 바깥 다각형과 별 모양 대각선
  function drawWeb(pts) {
    var svg = $('hubWeb');
    svg.innerHTML = '';
    var NS = 'http://www.w3.org/2000/svg';
    var poly = document.createElementNS(NS, 'polygon');
    poly.setAttribute('points', pts.map(function (p) { return p[0] + ',' + p[1]; }).join(' '));
    svg.appendChild(poly);

    var step = pts.length >= 5 ? 2 : 1;
    pts.forEach(function (p, i) {
      var q = pts[(i + step) % pts.length];
      var ln = document.createElementNS(NS, 'line');
      ln.setAttribute('x1', p[0]); ln.setAttribute('y1', p[1]);
      ln.setAttribute('x2', q[0]); ln.setAttribute('y2', q[1]);
      svg.appendChild(ln);
    });
  }

  // ------------------------------------------------------------- 난이도 바

  function renderLevels() {
    var bar = $('levelBar');
    bar.innerHTML = '';
    PROBLEMS.levels.forEach(function (lv) {
      var b = document.createElement('button');
      b.setAttribute('aria-selected', String(lv === session.level));
      b.setAttribute('data-level', lv);
      var dot = document.createElement('span');
      dot.className = 'dot ' + lv;
      b.appendChild(dot);
      b.appendChild(document.createTextNode(PROBLEMS.labels[lv]));
      if (session.mode !== 'practice') {
        var rec = recordFor(session.dateKey, lv);
        if (rec && rec.solved) {
          var c = document.createElement('span');
          c.className = 'check';
          c.textContent = '✓';
          b.appendChild(c);
        }
      } else {
        var left = practiceLeft(lv);
        if (left !== Infinity) {
          var n = document.createElement('span');
          n.className = 'left' + (left === 0 ? ' out' : '');
          n.textContent = left === 0 ? '\u00d7' : String(left);
          b.appendChild(n);
        }
      }
      b.onclick = function () {
        session.level = lv;
        if (session.mode === 'practice') startPractice(lv, null);
        else loadProblem(problemForDay(lv, dayNumberOf(dateFromKey(session.dateKey))));
      };
      bar.appendChild(b);
    });
  }

  // ------------------------------------------------------------- 아카이브

  function renderArchive() {
    var grid = $('archiveGrid');
    grid.innerHTML = '';
    var now = new Date();
    for (var i = 0; i < 35; i++) {
      var d = new Date(now.getFullYear(), now.getMonth(), now.getDate() - i);
      var k = keyOf(d);
      var day = store.days[k] || {};
      var solvedCount = PROBLEMS.levels.filter(function (lv) { return day[lv] && day[lv].solved; }).length;

      var shut = !isAdmin() && k !== TODAY_KEY;

      var el = document.createElement('button');
      el.className = 'day' + (k === TODAY_KEY ? ' today' : '') +
        (solvedCount ? ' done' : '') + (shut ? ' locked' : '');
      el.innerHTML = '<div class="d">' + d.getDate() + '</div>' +
        '<div class="m">' + (d.getMonth() + 1) + '월</div>' +
        '<div class="marks">' + (shut ? '\u00b7\u00b7\u00b7\u00b7' :
          PROBLEMS.levels.map(function (lv) {
            return (day[lv] && day[lv].solved) ? '\u25cf' : '\u25cb';
          }).join('')) + '</div>';
      if (shut) el.title = '관리자 키가 있어야 열 수 있습니다';

      (function (key, closed) {
        function open() {
          session.mode = (key === TODAY_KEY) ? 'daily' : 'archive';
          session.dateKey = key;
          switchView('daily', true);
          loadProblem(problemForDay(session.level, dayNumberOf(dateFromKey(key))));
        }
        el.onclick = closed ? function () { askAdminKey(open); } : open;
      })(k, shut);
      grid.appendChild(el);
    }

    $('archiveNote').textContent = IS_APP
      ? '지난 날짜도 모두 열 수 있습니다'
      : (store.admin ? '관리자 모드 · 지난 날짜도 열 수 있습니다'
                     : '지난 날짜는 관리자 키가 있어야 열립니다');
  }

  // ------------------------------------------------------------- 통계

  function renderStats() {
    var solvedByLevel = {}, uniqueByLevel = {};
    PROBLEMS.levels.forEach(function (lv) { solvedByLevel[lv] = 0; uniqueByLevel[lv] = {}; });
    var totalAttempts = 0, totalSolved = 0, daysActive = 0;

    Object.keys(store.days).forEach(function (k) {
      var day = store.days[k];
      var any = false;
      PROBLEMS.levels.forEach(function (lv) {
        var rec = day[lv];
        if (!rec) return;
        totalAttempts += rec.attempts || 0;
        if (rec.solved) {
          solvedByLevel[lv]++; totalSolved++; any = true;
          var p = problemForDay(lv, dayNumberOf(dateFromKey(k)));
          uniqueByLevel[lv][p.id] = true;
        }
      });
      if (any) daysActive++;
    });

    var acc = (totalSolved + store.practice.solved) === 0 ? 0 :
      Math.round(100 * (totalSolved + store.practice.solved) /
        Math.max(1, totalSolved + store.practice.solved + totalAttempts + store.practice.attempts));

    var cards = [
      { k: '현재 연속 학습일', v: effectiveStreak() + '일', sub: '오늘의 문제 기준' },
      { k: '최고 연속 기록', v: store.best + '일', sub: '' },
      { k: '해결한 일일 문제', v: String(totalSolved), sub: daysActive + '일 참여' },
      { k: '연습 모드 해결', v: String(store.practice.solved), sub: '기록에 영향 없음' },
      { k: '첫 시도 성공률', v: acc + '%', sub: '오답 시도 대비' }
    ];
    var grid = $('statGrid');
    grid.innerHTML = '';
    cards.forEach(function (c) {
      var el = document.createElement('div');
      el.className = 'stat';
      el.innerHTML = '<div class="k">' + c.k + '</div><div class="v">' + c.v + '</div>' +
        (c.sub ? '<div class="sub">' + c.sub + '</div>' : '');
      grid.appendChild(el);
    });

    var lvGrid = $('levelStats');
    lvGrid.innerHTML = '';
    PROBLEMS.levels.forEach(function (lv) {
      var total = PROBLEMS.byLevel[lv].length;
      var uniq = Object.keys(uniqueByLevel[lv]).length;
      var pct = Math.round(100 * uniq / total);
      var el = document.createElement('div');
      el.className = 'stat';
      el.innerHTML = '<div class="k">' + PROBLEMS.labels[lv] + '</div>' +
        '<div class="v">' + uniq + '<span class="sub"> / ' + total + '</span></div>' +
        '<div class="bar"><i style="width:' + pct + '%"></i></div>';
      lvGrid.appendChild(el);
    });
  }

  function renderStreak() {
    $('streakVal').textContent = effectiveStreak();
  }

  // ------------------------------------------------------------- 뷰 전환

  function switchView(view, keepSession) {
    document.body.dataset.view = view;
    $('hubView').classList.toggle('hidden', view !== 'hub');
    $('playView').classList.toggle('hidden', !(view === 'daily' || view === 'practice'));
    $('archiveView').classList.toggle('hidden', view !== 'archive');
    $('statsView').classList.toggle('hidden', view !== 'stats');
    window.scrollTo(0, 0);

    if (view === 'hub') renderHub();
    if (view === 'archive') renderArchive();
    if (view === 'stats') renderStats();
    if (view === 'hub' || keepSession) return;

    if (view === 'daily') {
      session.mode = 'daily';
      session.dateKey = TODAY_KEY;
      showLock(null);
      renderQuota();
      loadProblem(problemForDay(session.level, dayNumberOf(new Date())));
    } else if (view === 'practice') {
      startPractice(session.level, session.problem && session.problem.id);
    }
  }

  /*
   * 안드로이드 뒤로 가기.
   *
   *   이 사이트는 한 페이지 안에서 화면만 갈아 끼우는 구조라 웹뷰가 볼 때는
   *   방문 기록이 하나뿐이다. 그래서 앱에서 뒤로 가기를 누르면 갈 곳이 없다며
   *   바로 앱이 닫혔다. 여기서 '한 단계 뒤'가 무엇인지 알려 준다.
   *
   *   MainActivity 가 이 함수를 먼저 불러 보고, true 를 받으면 앱을 닫지 않는다.
   *   웹 브라우저에서는 아무도 부르지 않으므로 동작이 달라지지 않는다.
   */
  window.appBack = function () {
    // 연습장이 얹혀 있으면 그것부터 닫는다
    if (!$('padOverlay').classList.contains('hidden')) { padClose(); return true; }
    // 문제·아카이브·통계 화면이면 첫 화면으로
    if (document.body.dataset.view !== 'hub') { switchView('hub'); return true; }
    return false;                     // 첫 화면이라 더 갈 데가 없다
  };

  // ------------------------------------------------------------- 카운트다운

  function tickCountdown() {
    var now = new Date();
    var next = new Date(now.getFullYear(), now.getMonth(), now.getDate() + 1, 0, 0, 0);
    var s = Math.max(0, Math.floor((next - now) / 1000));
    var hh = String(Math.floor(s / 3600)).padStart(2, '0');
    var mm = String(Math.floor((s % 3600) / 60)).padStart(2, '0');
    var ss = String(s % 60).padStart(2, '0');
    $('resetVal').textContent = hh + ':' + mm + ':' + ss;
    if (s === 0) setTimeout(function () { location.reload(); }, 1500);
  }

  // ------------------------------------------------------------- 팔레트

  var PALETTE = [
    ['x\u00b2', '\u00b2'], ['x\u00b3', '\u00b3'], ['x\u207f', '^'],
    ['\u221a', '\u221a('], ['ln', 'ln('], ['e\u02e3', 'e^('],
    ['sin', 'sin('], ['cos', 'cos('], ['tan', 'tan('],
    ['arctan', 'atan('], ['arcsin', 'asin('], ['sinh', 'sinh('], ['cosh', 'cosh('],
    ['|\u00b7|', '|'], ['( )', '('], ['\u00b7', '\u00b7'], ['/', '/'],
    ['\u03c0', '\u03c0'], ['+C', '+C']
  ];

  function buildPalette() {
    var box = $('palette');
    PALETTE.forEach(function (pair) {
      var b = document.createElement('button');
      b.textContent = pair[0];
      b.onclick = function () {
        var inp = $('answerInput');
        var s = inp.selectionStart || inp.value.length;
        var e = inp.selectionEnd || s;
        inp.value = inp.value.slice(0, s) + pair[1] + inp.value.slice(e);
        inp.focus();
        inp.setSelectionRange(s + pair[1].length, s + pair[1].length);
        updatePreview();
      };
      box.appendChild(b);
    });
  }

  // ------------------------------------------------------------- 연습장

  /*
   * 손으로 풀어 보는 필기판. 문제를 위에 띄워 두고 그 아래 모눈종이에 쓴다.
   *
   *   필기는 비트맵이 아니라 획(stroke) 목록으로 들고 있다. 되돌리기가 공짜가 되고,
   *   화면을 돌리거나 창을 줄여도 다시 그리면 되고, 저장도 가볍다.
   *   좌표는 캔버스 가로폭으로 나눠 정규화해 둔다 — 가로세로를 같은 값으로 나누므로
   *   크기가 달라져도 글씨 비율이 찌그러지지 않는다.
   */

  var PAD_KEY = 'dailyIntegral.pad.v1';

  // 0번은 테마를 따라가야 해서(다크 모드에서 검은 글씨는 안 보인다) 그릴 때 값을 읽는다
  var PAD_COLORS = [
    { name: '먹', cssVar: '--ink' },
    { name: '파랑', hex: '#3b82c4' },
    { name: '빨강', hex: '#cf4257' },
    { name: '초록', hex: '#17916a' }
  ];
  var PAD_WIDTHS = [1.5, 2.6, 4.4];      // CSS 픽셀 기준 기본 굵기
  var PAD_ERASER = 7;                    // 지우개는 펜 굵기의 몇 배

  var pad = {
    ctx: null,
    w: 0, h: 0,                // 캔버스 CSS 크기
    strokes: [],               // 지금 문제의 획 목록
    byProblem: {},             // 문제 id -> 획 목록 (세션 동안 유지)
    problemId: null,
    cleared: null,             // '전체 지우기' 직전 상태 (되돌리기용)
    cur: null,                 // 그리는 중인 획
    mode: 'pen',
    color: 0,
    width: 1,
    penOnly: true,
    penSeen: false,            // 펜이 한 번이라도 닿았는지
    lastNag: 0,
    toastTimer: null,
    saveTimer: null
  };

  function padColor(i) {
    var c = PAD_COLORS[i] || PAD_COLORS[0];
    if (c.hex) return c.hex;
    var v = getComputedStyle(document.documentElement).getPropertyValue(c.cssVar);
    return (v || '').trim() || '#16202e';
  }

  // 기본값: 터치가 되는 기기(태블릿·휴대폰)에서만 '펜만'을 켠다.
  // 마우스밖에 없는 컴퓨터에서 켜 두면 아무것도 못 그리게 된다.
  function padPenOnlyDefault() {
    return (navigator.maxTouchPoints || 0) > 0;
  }

  function padToast(msg) {
    var t = $('padToast');
    if (!t) return;
    t.textContent = msg;
    t.classList.add('show');
    clearTimeout(pad.toastTimer);
    pad.toastTimer = setTimeout(function () { t.classList.remove('show'); }, 2400);
  }

  // --- 크기 맞추기 -------------------------------------------------

  function padResize() {
    var sheet = $('padSheet'), cv = $('padCanvas');
    if (!sheet || !cv) return;
    var r = sheet.getBoundingClientRect();
    if (!r.width || !r.height) return;
    var dpr = Math.min(window.devicePixelRatio || 1, 3);
    pad.w = r.width;
    pad.h = r.height;
    cv.width = Math.round(r.width * dpr);
    cv.height = Math.round(r.height * dpr);
    pad.ctx = cv.getContext('2d');
    pad.ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    padRedraw();
  }

  // --- 그리기 ------------------------------------------------------

  function padPrep(ctx, st) {
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    if (st.e) {
      ctx.globalCompositeOperation = 'destination-out';
      ctx.strokeStyle = 'rgba(0,0,0,1)';
    } else {
      ctx.globalCompositeOperation = 'source-over';
      ctx.strokeStyle = padColor(st.c);
    }
  }

  // 필압에 따라 굵기가 변해야 해서 마디마다 따로 긋는다.
  // 끝을 둥글게 하면 마디 이음매가 보이지 않는다.
  function padSegments(ctx, st, from) {
    var base = (PAD_WIDTHS[st.w] || PAD_WIDTHS[1]) * (st.e ? PAD_ERASER : 1);
    var W = pad.w;
    var pts = st.p;
    if (pts.length === 1 && from === 0) {          // 점 하나만 찍은 경우
      ctx.beginPath();
      ctx.arc(pts[0][0] * W, pts[0][1] * W, base * (0.45 + 0.95 * pts[0][2]) / 2, 0, 6.2832);
      ctx.fillStyle = st.e ? 'rgba(0,0,0,1)' : padColor(st.c);
      ctx.fill();
      return;
    }
    for (var i = Math.max(1, from); i < pts.length; i++) {
      var a = pts[i - 1], b = pts[i];
      ctx.lineWidth = base * (0.45 + 0.95 * (a[2] + b[2]) / 2);
      ctx.beginPath();
      ctx.moveTo(a[0] * W, a[1] * W);
      ctx.lineTo(b[0] * W, b[1] * W);
      ctx.stroke();
    }
  }

  function padRedraw() {
    var ctx = pad.ctx;
    if (!ctx) return;
    ctx.clearRect(0, 0, pad.w, pad.h);
    pad.strokes.forEach(function (st) { padPrep(ctx, st); padSegments(ctx, st, 0); });
    if (pad.cur) { padPrep(ctx, pad.cur); padSegments(ctx, pad.cur, 0); }
    ctx.globalCompositeOperation = 'source-over';
  }

  // --- 입력 --------------------------------------------------------

  function padPoint(e) {
    var r = $('padCanvas').getBoundingClientRect();
    var pr = (e.pressure > 0 && e.pressure <= 1) ? e.pressure : 0.5;
    return [
      Math.round((e.clientX - r.left) / r.width * 1e4) / 1e4,
      Math.round((e.clientY - r.top) / r.width * 1e4) / 1e4,
      Math.round(pr * 100) / 100
    ];
  }

  // 여기가 '펜만' 의 전부다. 손가락·손바닥은 pointerType 이 'touch' 라서 걸러진다.
  function padAccepts(e) {
    if (e.pointerType === 'pen') {
      if (!pad.penSeen) { pad.penSeen = true; padRenderTools(); }
      return true;
    }
    if (!pad.penOnly) return true;
    var now = Date.now();
    if (now - pad.lastNag > 2000) {
      pad.lastNag = now;
      padToast(e.pointerType === 'touch'
        ? '손가락으로는 그려지지 않습니다. 펜을 쓰거나 위의 “펜만”을 끄세요.'
        : '“펜만” 이 켜져 있습니다. 끄면 마우스로도 그릴 수 있습니다.');
    }
    return false;
  }

  function padDown(e) {
    if (!padAccepts(e)) return;
    e.preventDefault();
    // S펜 버튼을 누른 채 그으면 그 획만 지우개가 된다
    var erasing = pad.mode === 'eraser' || (e.buttons & 32) === 32 || e.button === 5;
    pad.cur = { c: pad.color, w: pad.width, e: erasing, p: [padPoint(e)] };
    try { $('padCanvas').setPointerCapture(e.pointerId); } catch (err) { /* 무시 */ }
    padPrep(pad.ctx, pad.cur);
    padSegments(pad.ctx, pad.cur, 0);
  }

  function padMove(e) {
    if (!pad.cur) return;
    e.preventDefault();
    var from = pad.cur.p.length;
    // 브라우저가 몰아 둔 중간 좌표까지 받아 오면 빠르게 그어도 각지지 않는다
    var evs = (typeof e.getCoalescedEvents === 'function') ? e.getCoalescedEvents() : null;
    if (evs && evs.length) {
      for (var i = 0; i < evs.length; i++) pad.cur.p.push(padPoint(evs[i]));
    } else {
      pad.cur.p.push(padPoint(e));
    }
    padPrep(pad.ctx, pad.cur);
    padSegments(pad.ctx, pad.cur, from);
  }

  function padUp(e) {
    if (!pad.cur) return;
    if (e) { try { $('padCanvas').releasePointerCapture(e.pointerId); } catch (err) { /* 무시 */ } }
    pad.strokes.push(pad.cur);
    pad.cur = null;
    pad.cleared = null;
    padSaveLater();
  }

  // --- 도구 --------------------------------------------------------

  function padSetMode(m) {
    pad.mode = m;
    $('padPen').classList.toggle('on', m === 'pen');
    $('padPen').setAttribute('aria-pressed', String(m === 'pen'));
    $('padEraser').classList.toggle('on', m === 'eraser');
    $('padEraser').setAttribute('aria-pressed', String(m === 'eraser'));
  }

  function padRenderTools() {
    var cols = $('padColors');
    cols.innerHTML = '';
    PAD_COLORS.forEach(function (c, i) {
      var b = document.createElement('button');
      b.className = 'swatch' + (i === pad.color ? ' on' : '');
      b.title = c.name;
      b.setAttribute('aria-label', c.name);
      var dot = document.createElement('i');
      dot.style.background = padColor(i);
      b.appendChild(dot);
      b.onclick = function () {
        pad.color = i;
        store.pad.color = i;
        save();
        padSetMode('pen');
        padRenderTools();
      };
      cols.appendChild(b);
    });

    var ws = $('padWidths');
    ws.innerHTML = '';
    PAD_WIDTHS.forEach(function (w, i) {
      var b = document.createElement('button');
      b.className = 'wbtn' + (i === pad.width ? ' on' : '');
      b.title = ['가늘게', '보통', '굵게'][i];
      b.setAttribute('aria-label', b.title);
      var dot = document.createElement('i');
      var d = 4 + i * 3;
      dot.style.width = d + 'px';
      dot.style.height = d + 'px';
      b.appendChild(dot);
      b.onclick = function () {
        pad.width = i;
        store.pad.width = i;
        save();
        padRenderTools();
      };
      ws.appendChild(b);
    });

    var po = $('padPenOnly');
    po.classList.toggle('on', pad.penOnly);
    po.setAttribute('aria-pressed', String(pad.penOnly));
    po.title = pad.penOnly
      ? '펜(S펜·애플펜슬)으로만 그려집니다. 손가락은 무시합니다.'
      : '손가락·마우스로도 그려집니다.';
  }

  function padUndo() {
    if (pad.strokes.length) {
      pad.strokes.pop();
    } else if (pad.cleared) {
      pad.strokes = pad.cleared;
      pad.cleared = null;
      padToast('전체 지우기를 되돌렸습니다.');
    } else {
      return;
    }
    padRedraw();
    padSaveLater();
  }

  function padClear() {
    if (!pad.strokes.length) return;
    pad.cleared = pad.strokes;
    pad.strokes = [];
    pad.byProblem[pad.problemId] = pad.strokes;
    padRedraw();
    padSaveLater();
    padToast('다 지웠습니다. 되돌리기로 되살릴 수 있습니다.');
  }

  // --- 저장 --------------------------------------------------------

  function padSaveLater() {
    clearTimeout(pad.saveTimer);
    pad.saveTimer = setTimeout(padSaveNow, 600);
  }

  function padSaveNow() {
    try {
      if (!pad.problemId) return;
      if (!pad.strokes.length) { localStorage.removeItem(PAD_KEY); return; }
      var json = JSON.stringify({ id: pad.problemId, strokes: pad.strokes });
      // 너무 길게 쓴 날은 저장을 건너뛴다. 화면의 필기는 그대로 남는다.
      if (json.length > 600000) return;
      localStorage.setItem(PAD_KEY, json);
    } catch (e) { /* 용량 초과·시크릿 모드 */ }
  }

  function padLoadSaved() {
    try {
      var raw = localStorage.getItem(PAD_KEY);
      if (!raw) return;
      var d = JSON.parse(raw);
      if (d && d.id && Array.isArray(d.strokes)) pad.byProblem[d.id] = d.strokes;
    } catch (e) { /* 무시 */ }
  }

  // --- 열고 닫기 ---------------------------------------------------

  function padSyncProblem() {
    var id = session.problem ? session.problem.id : null;
    pad.problemId = id;
    if (!id) { pad.strokes = []; return; }
    if (!pad.byProblem[id]) pad.byProblem[id] = [];
    pad.strokes = pad.byProblem[id];
    pad.cleared = null;
  }

  function padOpen() {
    if (!session.problem) return;
    padSyncProblem();

    var p = session.problem;
    var isDef = p.value !== undefined;
    var bounds = isDef ? '_{' + p.loLatex + '}^{' + p.hiLatex + '}' : '';
    renderTex($('padProblem'), '\\int' + bounds + ' ' + p.latex + '\\,dx', false,
      '∫ ' + p.integrand + ' dx');

    document.body.classList.add('pad-open');
    $('padOverlay').classList.remove('hidden');
    $('answerInput').blur();
    padRenderTools();
    padSetMode(pad.mode);
    // 레이아웃이 잡힌 다음에 크기를 재야 캔버스가 0 이 되지 않는다
    requestAnimationFrame(padResize);
  }

  function padClose() {
    padSaveNow();
    $('padOverlay').classList.add('hidden');
    document.body.classList.remove('pad-open');
  }

  function padInit() {
    pad.color = store.pad.color || 0;
    pad.width = (store.pad.width === undefined || store.pad.width === null) ? 1 : store.pad.width;
    pad.penOnly = (store.pad.penOnly === null || store.pad.penOnly === undefined)
      ? padPenOnlyDefault() : !!store.pad.penOnly;
    padLoadSaved();

    $('padBtn').onclick = padOpen;
    $('padClose').onclick = padClose;
    $('padPen').onclick = function () { padSetMode('pen'); };
    $('padEraser').onclick = function () { padSetMode('eraser'); };
    $('padUndo').onclick = padUndo;
    $('padClear').onclick = padClear;
    $('padPenOnly').onclick = function () {
      pad.penOnly = !pad.penOnly;
      store.pad.penOnly = pad.penOnly;
      save();
      padRenderTools();
      padToast(pad.penOnly
        ? '펜으로만 그려집니다. 손을 얹어도 선이 그어지지 않습니다.'
        : '손가락·마우스로도 그릴 수 있습니다.');
    };

    var cv = $('padCanvas');
    cv.addEventListener('pointerdown', padDown);
    cv.addEventListener('pointermove', padMove);
    cv.addEventListener('pointerup', padUp);
    cv.addEventListener('pointercancel', function (e) { padUp(e); });
    cv.addEventListener('pointerleave', function (e) { padUp(e); });
    // 펜 버튼을 눌렀을 때 뜨는 브라우저 기본 메뉴를 막는다
    cv.addEventListener('contextmenu', function (e) { e.preventDefault(); });

    window.addEventListener('resize', function () {
      if (!$('padOverlay').classList.contains('hidden')) padResize();
    });
    document.addEventListener('keydown', function (e) {
      if ($('padOverlay').classList.contains('hidden')) return;
      if (e.key === 'Escape') { e.preventDefault(); padClose(); }
      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') { e.preventDefault(); padUndo(); }
    });
  }

  // ------------------------------------------------------------- 초기화

  function applyTheme() {
    document.documentElement.setAttribute('data-theme', store.theme);
    $('themeBtn').textContent = store.theme === 'dark' ? '☾' : '☀';
  }

  function init() {
    applyTheme();
    buildPalette();
    $('bankCount').textContent = PROBLEMS.all.length;

    $('themeBtn').onclick = function () {
      store.theme = store.theme === 'dark' ? 'light' : 'dark';
      save(); applyTheme();
    };

    $('backBtn').onclick = function () { switchView('hub'); };

    renderAdminBtn();
    $('adminBtn').onclick = function () {
      if (store.admin) lockAdmin(); else askAdminKey();
    };

    $('submitBtn').onclick = check;
    padInit();
    $('answerInput').addEventListener('input', onAnswerInput);
    $('answerInput').addEventListener('keydown', function (e) {
      if (e.key === 'Enter') { e.preventDefault(); check(); }
    });

    $('hintBtn').onclick = function () {
      var p = session.problem;
      if (session.hintsShown >= p.hints.length) {
        showFeedback('info', '더 이상 힌트가 없습니다. 해설 보기를 눌러 보세요.');
        return;
      }
      appendHint(session.hintsShown);
      session.hintsShown++;
      if (session.mode !== 'practice') {
        ensureRecord(session.dateKey, session.level).hints = session.hintsShown;
        save();
      }
      updateAttemptChip();
    };

    $('revealBtn').onclick = function () { revealSolution(false); };

    $('nextBtn').onclick = function () {
      startPractice(session.level, session.problem && session.problem.id, true);
    };

    $('resetDataBtn').onclick = function () {
      if (!confirm('저장된 기록을 모두 지웁니다. 계속할까요?')) return;
      store = blankStore();
      save();
      applyTheme();
      renderStreak(); renderStats(); renderArchive(); renderLevels();
      switchView('hub');
    };

    renderStreak();
    renderArchive();
    renderStats();
    switchView('hub');

    tickCountdown();
    setInterval(tickCountdown, 1000);
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
