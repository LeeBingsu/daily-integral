/*
 * generate.js - 문제 은행 생성기.
 *
 *   node generate.js        problems.js 를 다시 만든다
 *
 * 문제는 손으로 500개를 쓰는 대신 "families"(매개변수화된 유형)에서 뽑아낸다.
 * 생성된 모든 문항은 마지막에 기준 부정적분을 수치 미분해 피적분함수와
 * 일치하는지 검사하므로, 템플릿이 틀리면 파일이 만들어지지 않는다.
 */
'use strict';

var fs = require('fs');
var M = require('./parser.js');

// ------------------------------------------------------------------ 헬퍼

function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = b; b = a % b; a = t; } return a || 1; }
function red(n, d) { if (d < 0) { n = -n; d = -d; } var g = gcd(n, d); return [n / g, d / g]; }

// (n/d)·body 를 파서가 읽을 수 있는 ASCII 로
function C(n, d, body) {
  var r = red(n, d); n = r[0]; d = r[1];
  if (n === 0) return '0';
  if (body === undefined || body === '1') return d === 1 ? String(n) : '(' + n + '/' + d + ')';
  if (body.indexOf('1/') === 0) {                 // 5*1/x 대신 5/x 로
    var rest = body.slice(2);
    if (d === 1) return n === 1 ? body : n + '/' + rest;
    return '(' + n + ')/(' + d + '*' + rest + ')';
  }
  if (d === 1) return n === 1 ? body : n === -1 ? '-' + body : n + '*' + body;
  return '(' + n + '/' + d + ')*' + body;
}

// 계수를 앞에 붙인 변수 표기: K(2) -> '2x', K(1) -> 'x', K(-1) -> '-x'
function K(k, v) { v = v || 'x'; return k === 1 ? v : k === -1 ? '-' + v : k + v; }

// 항들을 더한다. '+ -' 는 '-' 로 정리한다.
function S() {
  var terms = [].slice.call(arguments).filter(function (t) { return t && t !== '0'; });
  return terms.join(' + ').replace(/\+ -/g, '- ');
}

// 자주 쓰는 표본 구간
var D = {
  poly:  [0.3, 2.4],
  pos:   [0.35, 2.6],       // x>0 (로그, 분수 거듭제곱)
  all:   [-1.5, 1.7],
  trig:  [0.25, 1.15],      // tan/sec 의 극점 회피
  trigW: [0.25, 2.85],      // sin/cos 전용
  unit:  [-0.72, 0.72],     // arcsin, sqrt(1-x^2)
  gt1:   [1.35, 3.4],       // arcosh, sqrt(x^2-1)
  lnln:  [1.4, 4.2],
  hyp:   [0.25, 1.6],
  hypP:  [0.35, 2.0]
};

// tan/sec 는 x=pi/(2k), cot/csc 는 x=0 과 pi/k 에 극점이 있다.
// 계수 k 에 맞춰 구간을 좁혀 한 가지(branch) 안에 머물게 한다.
// LaTeX 조립: 계수 1 은 생략, 분모 1 은 분수로 쓰지 않는다
function KL(k, tex) { return k === 1 ? tex : k === -1 ? '-' + tex : k + tex; }
function KC(k) { return k === 1 ? '' : k === -1 ? '-' : String(k); }   // 계수만 (뒤에 LaTeX 명령이 붙는 자리)
function FR(num, den) {
  if (den === 1) return num === '1' ? '' : num;      // 계수 1 은 아예 쓰지 않는다
  if (den === -1) return '-' + num;
  return '\\dfrac{' + num + '}{' + den + '}';
}

// sqrt(n/d) 를 가능한 한 간단히 (sqrt(16) -> 4, sqrt(2/8) -> 1/2)
function isSq(n) { var r = Math.round(Math.sqrt(n)); return r * r === n ? r : 0; }
function SQ(n, d) {
  var r = red(n, d === undefined ? 1 : d); n = r[0]; d = r[1];
  var sn = isSq(n), sd = isSq(d);
  if (sn && sd) return C(sn, sd);
  return d === 1 ? 'sqrt(' + n + ')' : 'sqrt(' + n + '/' + d + ')';
}

// a=1 이면 'x/1' 대신 그냥 'x' 를 쓴다
function X(a) { return a === 1 ? 'x' : 'x/' + a; }
function XL(a) { return a === 1 ? 'x' : '\\dfrac{x}{' + a + '}'; }

function dTrig(k) { return [0.25 / k, 1.15 / k]; }
function dCot(k)  { return [0.5 / k, 2.3 / k]; }

// ---- 표기 정리 --------------------------------------------------------
// 계수·분모가 1 인 자리를 지운다. 템플릿마다 처리하는 대신 한곳에서 정리한다.
function tidyAscii(t) {
  return t
    .replace(/\/1(?![0-9.])/g, '')            // (x+1)/1 -> (x+1)
    .replace(/(?<![0-9.])1(?=[a-zA-Z(])/g, '');  // 1x^2 -> x^2, 1sin(x) -> sin(x)
}

// \dfrac{...}{1} 을 중괄호 짝을 세어 정확히 벗겨낸다
function stripDenomOne(tex) {
  ['\\dfrac{', '\\frac{'].forEach(function (head) {
    for (;;) {
      var i = tex.indexOf(head);
      var found = false;
      while (i >= 0) {
        var j = i + head.length, depth = 1;
        while (j < tex.length && depth > 0) {
          if (tex[j] === '{') depth++;
          else if (tex[j] === '}') depth--;
          j++;
        }
        if (tex.slice(j, j + 3) === '{1}') {
          tex = tex.slice(0, i) + tex.slice(i + head.length, j - 1) + tex.slice(j + 3);
          found = true;
          break;
        }
        i = tex.indexOf(head, i + 1);
      }
      if (!found) break;
    }
  });
  return tex;
}

function tidyTex(t) {
  return stripDenomOne(t)
    .replace(/--/g, '+')                          // -(-2) 를 + 로
    .replace(/\+\s*\+/g, '+');
}

var out = [];
var seen = Object.create(null);

function add(level, topic, integrand, answer, o) {
  o = o || {};
  integrand = tidyAscii(integrand.replace(/\^1(?![0-9])/g, ''));
  answer = tidyAscii(answer.replace(/\^1(?![0-9])/g, ''));
  var key = integrand.replace(/\s+/g, '');
  if (seen[key]) return;
  seen[key] = true;
  out.push({
    level: level,
    topic: topic,
    integrand: integrand,
    latex: tidyTex(o.latex || M.latexOf(integrand)),
    answer: answer,
    answerLatex: tidyTex((o.answerLatex || M.latexOf(answer, { lnAbs: o.lnAbs })) + '+C'),
    domain: o.domain || D.poly,
    hints: (o.hints || []).map(tidyTex),
    steps: (o.steps || []).map(tidyTex)
  });
}

// ---------------------------------------------------------------- 정적분 문항
// 부정적분 문항과 달리 answer/domain 대신 lo/hi/value 를 갖는다.
// 채점은 "값이 맞는가"로, 검증은 이중지수 구적으로 한다.

function limVal(src) {
  if (src === 'inf') return Infinity;
  if (src === '-inf') return -Infinity;
  return M.compile(src)(0);
}
function limTex(src) {
  if (src === 'inf') return '\\infty';
  if (src === '-inf') return '-\\infty';
  return tidyTex(M.latexOf(src));
}

function addDef(level, topic, integrand, value, o) {
  o = o || {};
  integrand = tidyAscii(integrand.replace(/\^1(?![0-9])/g, ''));
  var key = 'DEF:' + integrand.replace(/\s+/g, '') + '|' + o.lo + '|' + o.hi;
  if (seen[key]) return;
  seen[key] = true;
  out.push({
    level: level,
    topic: topic,
    integrand: integrand,
    latex: tidyTex(o.latex || M.latexOf(integrand)),
    lo: o.lo, hi: o.hi,
    loLatex: o.loLatex || limTex(o.lo),
    hiLatex: o.hiLatex || limTex(o.hi),
    value: value,
    valueLatex: tidyTex(o.valueLatex || M.latexOf(value)),
    hints: (o.hints || []).map(tidyTex),
    steps: (o.steps || []).map(tidyTex)
  });
}

// ================================================================== 쉬움

// 거듭제곱 법칙 (단항)
[2, 3, -4, 7].forEach(function (a) {
  [2, 3, 4, 5].forEach(function (n) {
    add('easy', '거듭제곱 법칙', K(a, 'x^' + n), C(a, n + 1, 'x^' + (n + 1)), {
      hints: ['$\\int x^{n}dx=\\dfrac{x^{n+1}}{n+1}$ 을 그대로 쓴다.',
              '지수를 $' + (n + 1) + '$ 로 올리고 그 값으로 나눈다.'],
      steps: ['$\\int ' + K(a, 'x^{' + n + '}') + 'dx = ' + KC(a) + '\\cdot\\dfrac{x^{' + (n + 1) + '}}{' + (n + 1) + '}$',
              '$= ' + M.latexOf(C(a, n + 1, 'x^' + (n + 1))) + '$']
    });
  });
});

// 다항식
[[3, 2, -4, 1, 5], [2, 3, 5, 1, -3], [6, 2, -2, 1, 7], [4, 3, 3, 2, -1],
 [5, 4, -6, 2, 2], [1, 5, 4, 3, -8], [3, 3, -5, 2, 6], [8, 2, -3, 1, 1],
 [7, 3, -4, 4, 3], [3, 4, -2, 2, 5]
].forEach(function (p) {
  var a = p[0], n = p[1], b = p[2], m = p[3], c = p[4];
  var integ = S(K(a, 'x^' + n), K(b, 'x^' + m), String(c));
  var ans = S(C(a, n + 1, 'x^' + (n + 1)), C(b, m + 1, 'x^' + (m + 1)), C(c, 1, 'x'));
  add('easy', '다항함수', integ, ans, {
    hints: ['각 항을 따로 적분한 뒤 더한다.', '상수항 $' + c + '$ 의 적분은 $' + c + 'x$ 다.'],
    steps: ['$\\int ' + M.latexOf(K(a, 'x^' + n)) + 'dx = ' + M.latexOf(C(a, n + 1, 'x^' + (n + 1))) + '$',
            '$\\int ' + M.latexOf(K(b, 'x^' + m)) + 'dx = ' + M.latexOf(C(b, m + 1, 'x^' + (m + 1))) + '$',
            '$\\int ' + c + '\\,dx = ' + c + 'x$']
  });
});

// 음의 지수
[1, 3, 6, -2].forEach(function (a) {
  [2, 3, 4].forEach(function (n) {
    add('easy', '거듭제곱 법칙', C(a, 1, '1/x^' + n), C(a, 1 - n, '1/x^' + (n - 1)), {
      domain: D.pos,
      hints: ['$x^{-' + n + '}$ 으로 고쳐 쓴다.', '지수 $-' + n + '$ 에 $1$ 을 더하면 $' + (1 - n) + '$ 이다.'],
      steps: ['$\\dfrac{' + a + '}{x^{' + n + '}} = ' + a + 'x^{-' + n + '}$',
              '$\\int ' + a + 'x^{-' + n + '}dx = ' + M.latexOf(C(a, 1 - n, '1/x^' + (n - 1))) + '$']
  });
  });
});

// 1/x 형태
[1, 2, 3, 5, 7, -4].forEach(function (a) {
  add('easy', '로그', C(a, 1, '1/x'), C(a, 1, 'ln(x)'), {
    domain: D.pos, lnAbs: true,
    hints: ['$\\int\\dfrac{1}{x}dx$ 는 거듭제곱 법칙의 예외다.', '상수 $' + a + '$ 는 적분 밖으로 뺀다.'],
    steps: ['$' + KC(a) + '\\int\\dfrac{1}{x}dx = ' + KC(a) + '\\ln|x|$']
  });
});

// 지수함수
[1, 2, -5].forEach(function (a) {
  [1, 2, 3, -2].forEach(function (k) {
    add('easy', '지수함수', C(a, 1, 'e^(' + K(k) + ')'), C(a, k, 'e^(' + K(k) + ')'), {
      domain: D.all,
      hints: ['$u=' + K(k) + '$ 로 두면 $du=' + KC(k) + '\\,dx$ 다.', '안쪽 $x$ 의 계수 $' + k + '$ 로 나눈다.'],
      steps: ['$u=' + K(k) + ',\\; du=' + KC(k) + '\\,dx$',
              '$\\dfrac{' + a + '}{' + k + '}\\int e^{u}du = ' + M.latexOf(C(a, k, 'e^(' + K(k) + ')')) + '$']
    });
  });
});

// 일반 밑의 지수함수
[2, 3, 5].forEach(function (b) {
  [1, 2].forEach(function (a) {
    add('easy', '지수함수', C(a, 1, b + '^x'), C(a, 1, b + '^x/ln(' + b + ')'), {
      domain: D.all,
      hints: ['$' + b + '^{x}=e^{x\\ln ' + b + '}$ 로 바꾼다.', '밑의 자연로그 $\\ln ' + b + '$ 로 나눈다.'],
      steps: ['$' + b + '^{x}=e^{x\\ln ' + b + '}$',
              '$\\int ' + b + '^{x}dx=\\dfrac{' + b + '^{x}}{\\ln ' + b + '}$']
    });
  });
});

// 사인 / 코사인
[1, 2, -4].forEach(function (a) {
  [1, 2, 3, 4].forEach(function (k) {
    add('easy', '삼각함수', C(a, 1, 'sin(' + K(k) + ')'), C(-a, k, 'cos(' + K(k) + ')'), {
      domain: D.trigW,
      hints: ['$\\int\\sin u\\,du=-\\cos u$ 다.', '안쪽 계수 $' + k + '$ 로 나눈다.'],
      steps: ['$u=' + K(k) + ',\\;du=' + KC(k) + '\\,dx$',
              '$= ' + M.latexOf(C(-a, k, 'cos(' + K(k) + ')')) + '$']
    });
    add('easy', '삼각함수', C(a, 1, 'cos(' + K(k) + ')'), C(a, k, 'sin(' + K(k) + ')'), {
      domain: D.trigW,
      hints: ['$\\int\\cos u\\,du=\\sin u$ 다.', '안쪽 계수 $' + k + '$ 로 나눈다.'],
      steps: ['$u=' + K(k) + ',\\;du=' + KC(k) + '\\,dx$',
              '$= ' + M.latexOf(C(a, k, 'sin(' + K(k) + ')')) + '$']
    });
  });
});

// 기본 삼각 적분표
[1, 2].forEach(function (k) {
  add('easy', '삼각함수', 'sec(' + K(k) + ')^2', C(1, k, 'tan(' + K(k) + ')'), {
    domain: dTrig(k),
    hints: ['$\\tan u$ 의 도함수가 $\\sec^{2}u$ 다.', '안쪽 계수 $' + k + '$ 로 나눈다.'],
    steps: ['$\\dfrac{d}{dx}\\tan ' + K(k) + ' = ' + KC(k) + '\\sec^{2}' + K(k) + '$']
  });
  add('easy', '삼각함수', 'csc(' + K(k) + ')^2', C(-1, k, 'cot(' + K(k) + ')'), {
    domain: dCot(k),
    hints: ['$\\cot u$ 의 도함수는 $-\\csc^{2}u$ 다.', '부호를 뒤집는다.'],
    steps: ['$\\dfrac{d}{dx}(-\\cot ' + K(k) + ') = ' + KC(k) + '\\csc^{2}' + K(k) + '$']
  });
  add('easy', '삼각함수', 'sec(' + K(k) + ')tan(' + K(k) + ')', C(1, k, 'sec(' + K(k) + ')'), {
    domain: dTrig(k),
    hints: ['$\\sec u$ 의 도함수를 그대로 떠올린다.', '치환이 필요 없다.'],
    steps: ['$\\dfrac{d}{dx}\\sec ' + K(k) + ' = ' + KC(k) + '\\sec ' + K(k) + '\\tan ' + K(k) + '$']
  });
  add('easy', '삼각함수', 'csc(' + K(k) + ')cot(' + K(k) + ')', C(-1, k, 'csc(' + K(k) + ')'), {
    domain: dCot(k),
    hints: ['$\\csc u$ 의 도함수는 $-\\csc u\\cot u$ 다.', '부호에 주의한다.'],
    steps: ['$\\dfrac{d}{dx}(-\\csc ' + K(k) + ') = ' + KC(k) + '\\csc ' + K(k) + '\\cot ' + K(k) + '$']
  });
});

// 1차식 치환
[2, 3].forEach(function (a) {
  [1, -1, 3].forEach(function (b) {
    [3, 4].forEach(function (n) {
      var u = '(' + K(a) + (b < 0 ? ' - ' + (-b) : ' + ' + b) + ')';
      add('easy', '치환(1차식)', u + '^' + n, C(1, a * (n + 1), u + '^' + (n + 1)), {
        domain: [0.2, 1.4],
        hints: ['전개하지 말고 $u=' + K(a) + (b < 0 ? b : '+' + b) + '$ 로 둔다.',
                '$du=' + KC(a) + '\\,dx$ 이므로 마지막에 $' + a + '$ 로 나눈다.'],
        steps: ['$u=' + K(a) + (b < 0 ? b : '+' + b) + ',\\;du=' + KC(a) + '\\,dx$',
                '$\\dfrac{1}{' + a + '}\\cdot\\dfrac{u^{' + (n + 1) + '}}{' + (n + 1) + '} = ' +
                M.latexOf(C(1, a * (n + 1), u + '^' + (n + 1))) + '$']
      });
    });
  });
});

// 1/(ax+b)
[2, 3].forEach(function (a) {
  [1, 3, -1].forEach(function (b) {
    var u = '(' + K(a) + (b < 0 ? ' - ' + (-b) : ' + ' + b) + ')';
    add('easy', '치환(1차식)', '1/' + u, C(1, a, 'ln' + u), {
      domain: [0.6, 2.6], lnAbs: true,
      hints: ['분모가 $1$ 차식이면 결과는 로그다.', '$du=' + KC(a) + '\\,dx$ 이므로 $' + a + '$ 로 나눈다.'],
      steps: ['$u=' + K(a) + (b < 0 ? b : '+' + b) + ',\\;du=' + KC(a) + '\\,dx$',
              '$\\dfrac{1}{' + a + '}\\int\\dfrac{du}{u} = ' + M.latexOf(C(1, a, 'ln' + u), { lnAbs: true }) + '$']
    });
  });
});

// 역삼각함수 기본형
[1, 3, 5].forEach(function (a) {
  add('easy', '역삼각함수', C(a, 1, '1/(1+x^2)'), C(a, 1, 'atan(x)'), {
    domain: D.all,
    hints: ['$\\arctan x$ 의 도함수 형태다.', '상수 $' + a + '$ 만 앞으로 뺀다.'],
    steps: ['$\\dfrac{d}{dx}\\arctan x=\\dfrac{1}{1+x^{2}}$']
  });
});
[1, 2, 4].forEach(function (a) {
  add('easy', '역삼각함수', C(a, 1, '1/sqrt(1-x^2)'), C(a, 1, 'asin(x)'), {
    domain: D.unit,
    hints: ['$\\arcsin x$ 의 도함수 형태다.', '적분표에 그대로 있는 꼴이다.'],
    steps: ['$\\dfrac{d}{dx}\\arcsin x=\\dfrac{1}{\\sqrt{1-x^{2}}}$']
  });
});

// 전개 후 적분
[[1, 3], [2, -1], [-2, 5], [3, 4], [1, -4], [4, -3]].forEach(function (p) {
  var a = p[0], b = p[1];
  var integ = '(x' + (a < 0 ? ' - ' + (-a) : ' + ' + a) + ')(x' + (b < 0 ? ' - ' + (-b) : ' + ' + b) + ')';
  var ans = S('x^3/3', C(a + b, 2, 'x^2'), C(a * b, 1, 'x'));
  add('easy', '전개 후 적분', integ, ans, {
    hints: ['먼저 곱을 전개한다.', '$x^{2}' + (a + b >= 0 ? '+' : '') + (a + b) + 'x' + (a * b >= 0 ? '+' : '') + (a * b) + '$ 를 적분한다.'],
    steps: ['$' + M.latexOf(integ) + ' = x^{2}' + (a + b >= 0 ? '+' : '') + (a + b) + 'x' + (a * b >= 0 ? '+' : '') + (a * b) + '$',
            '$\\int = ' + M.latexOf(ans) + '$']
  });
});

// 분수 지수
[1, 2, 3].forEach(function (a) {
  add('easy', '거듭제곱 법칙', C(a, 1, 'sqrt(x)'), C(2 * a, 3, 'x^(3/2)'), {
    domain: D.pos,
    hints: ['$\\sqrt{x}=x^{1/2}$ 로 바꾼다.', '지수에 $1$ 을 더하면 $3/2$ 다.'],
    steps: ['$\\sqrt{x}=x^{1/2}$', '$\\int x^{1/2}dx=\\dfrac{2}{3}x^{3/2}$']
  });
});
[[1, 3], [2, 3], [3, 2], [4, 3], [5, 2], [5, 3]].forEach(function (p) {
  var pn = p[0], q = p[1];
  add('easy', '거듭제곱 법칙', 'x^(' + pn + '/' + q + ')', C(q, pn + q, 'x^((' + (pn + q) + ')/' + q + ')'), {
    domain: D.pos,
    hints: ['지수 $\\dfrac{' + pn + '}{' + q + '}$ 에 $1$ 을 더하면 $\\dfrac{' + (pn + q) + '}{' + q + '}$ 다.',
            '분수 지수는 그 역수를 곱한다고 생각한다.'],
    steps: ['$\\int x^{' + pn + '/' + q + '}dx=\\dfrac{x^{' + (pn + q) + '/' + q + '}}{' + (pn + q) + '/' + q + '}$',
            '$= ' + M.latexOf(C(q, pn + q, 'x^((' + (pn + q) + ')/' + q + ')')) + '$']
  });
});

// 쌍곡선함수 기본
[1, 2].forEach(function (a) {
  [1, 2, 3].forEach(function (k) {
    add('easy', '쌍곡선함수', C(a, 1, 'sinh(' + K(k) + ')'), C(a, k, 'cosh(' + K(k) + ')'), {
      domain: D.hyp,
      hints: ['$\\sinh$ 를 적분하면 $\\cosh$ 다. 삼각함수와 달리 부호가 바뀌지 않는다.',
              '안쪽 계수 $' + k + '$ 로 나눈다.'],
      steps: ['$\\dfrac{d}{dx}\\cosh ' + K(k) + ' = ' + KC(k) + '\\sinh ' + K(k) + '$',
              '$= ' + M.latexOf(C(a, k, 'cosh(' + K(k) + ')')) + '$']
    });
    add('easy', '쌍곡선함수', C(a, 1, 'cosh(' + K(k) + ')'), C(a, k, 'sinh(' + K(k) + ')'), {
      domain: D.hyp,
      hints: ['$\\cosh$ 를 적분하면 $\\sinh$ 다.', '안쪽 계수 $' + k + '$ 로 나눈다.'],
      steps: ['$\\dfrac{d}{dx}\\sinh ' + K(k) + ' = ' + KC(k) + '\\cosh ' + K(k) + '$',
              '$= ' + M.latexOf(C(a, k, 'sinh(' + K(k) + ')')) + '$']
    });
  });
});
[1, 2, 3].forEach(function (k) {
  add('easy', '쌍곡선함수', 'sech(' + K(k) + ')^2', C(1, k, 'tanh(' + K(k) + ')'), {
    domain: D.hyp,
    hints: ['$\\tanh u$ 의 도함수가 $\\operatorname{sech}^{2}u$ 다.', '삼각함수의 $\\sec^{2}$ 와 같은 자리다.'],
    steps: ['$\\dfrac{d}{dx}\\tanh ' + K(k) + ' = ' + KC(k) + '\\operatorname{sech}^{2}' + K(k) + '$']
  });
  add('easy', '쌍곡선함수', 'csch(' + K(k) + ')^2', C(-1, k, 'coth(' + K(k) + ')'), {
    domain: D.hypP,
    hints: ['$\\coth u$ 의 도함수는 $-\\operatorname{csch}^{2}u$ 다.', '부호를 뒤집는다.'],
    steps: ['$\\dfrac{d}{dx}(-\\coth ' + K(k) + ') = ' + KC(k) + '\\operatorname{csch}^{2}' + K(k) + '$']
  });
});

// 삼각 항등식으로 차수 낮추기
[1, 2].forEach(function (k) {
  add('easy', '삼각항등식', 'tan(' + K(k) + ')^2', S(C(1, k, 'tan(' + K(k) + ')'), '-x'), {
    domain: dTrig(k),
    hints: ['$\\tan^{2}u=\\sec^{2}u-1$ 항등식을 쓴다.', '두 항 모두 기본 적분이다.'],
    steps: ['$\\tan^{2}' + K(k) + ' = \\sec^{2}' + K(k) + ' - 1$',
            '$\\int = ' + M.latexOf(S(C(1, k, 'tan(' + K(k) + ')'), '-x')) + '$']
  });
  add('easy', '삼각항등식', 'cot(' + K(k) + ')^2', S(C(-1, k, 'cot(' + K(k) + ')'), '-x'), {
    domain: dCot(k),
    hints: ['$\\cot^{2}u=\\csc^{2}u-1$ 을 쓴다.', '부호에 주의한다.'],
    steps: ['$\\cot^{2}' + K(k) + ' = \\csc^{2}' + K(k) + ' - 1$',
            '$\\int = ' + M.latexOf(S(C(-1, k, 'cot(' + K(k) + ')'), '-x')) + '$']
  });
});

// 항별로 쪼개기
[[1, 1], [2, 3], [3, -2], [-1, 4]].forEach(function (p) {
  var a = p[0], b = p[1];
  add('easy', '기본 적분', S(C(a, 1, 'e^x'), C(b, 1, '1/x')), S(C(a, 1, 'e^x'), C(b, 1, 'ln(x)')), {
    domain: D.pos, lnAbs: true,
    hints: ['두 항을 따로 적분한다.', '$e^{x}$ 는 적분해도 그대로다.'],
    steps: ['$\\int ' + M.latexOf(C(a, 1, 'e^x')) + 'dx = ' + M.latexOf(C(a, 1, 'e^x')) + '$',
            '$\\int ' + M.latexOf(C(b, 1, '1/x')) + 'dx = ' + M.latexOf(C(b, 1, 'ln(x)'), { lnAbs: true }) + '$']
  });
  add('easy', '기본 적분', '(' + K(a, 'x^2') + (b < 0 ? ' - ' + (-b) : ' + ' + b) + ')/x',
      S(C(a, 2, 'x^2'), C(b, 1, 'ln(x)')), {
    domain: D.pos, lnAbs: true,
    hints: ['분자를 분모로 각각 나눠 항을 분리한다.',
            '$' + M.latexOf(K(a, 'x')) + ' + \\dfrac{' + b + '}{x}$ 가 된다.'],
    steps: ['$\\dfrac{' + M.latexOf(K(a, 'x^2') + (b < 0 ? b : '+' + b)) + '}{x} = ' +
            M.latexOf(S(K(a, 'x'), C(b, 1, '1/x'))) + '$',
            '$\\int = ' + M.latexOf(S(C(a, 2, 'x^2'), C(b, 1, 'ln(x)')), { lnAbs: true }) + '$']
  });
});

// ================================================================== 보통

// u = x^n 치환
[1, 2, 3, -1].forEach(function (k) {
  add('medium', '치환적분', 'x*e^(' + K(k, 'x^2') + ')', C(1, 2 * k, 'e^(' + K(k, 'x^2') + ')'), {
    domain: [0.15, 1.3],
    hints: ['$u=' + K(k, 'x^{2}') + '$ 로 두면 $du=' + (2 * k) + 'x\\,dx$ 다.', '앞의 $x$ 가 $du$ 를 만들어 준다.'],
    steps: ['$u=' + K(k, 'x^{2}') + ',\\;du=' + (2 * k) + 'x\\,dx$',
            '$\\dfrac{1}{' + (2 * k) + '}\\int e^{u}du = ' + M.latexOf(C(1, 2 * k, 'e^(' + K(k, 'x^2') + ')')) + '$']
  });
});
[2, 3, 4].forEach(function (n) {
  add('medium', '치환적분', 'x^' + (n - 1) + '*e^(x^' + n + ')', C(1, n, 'e^(x^' + n + ')'), {
    domain: [0.15, 1.15],
    hints: ['$u=x^{' + n + '}$ 로 두면 $du=' + n + 'x^{' + (n - 1) + '}dx$ 다.', '분자가 $du$ 와 상수배로 맞는다.'],
    steps: ['$u=x^{' + n + '},\\;du=' + n + 'x^{' + (n - 1) + '}dx$',
            '$\\dfrac{1}{' + n + '}\\int e^{u}du = ' + M.latexOf(C(1, n, 'e^(x^' + n + ')')) + '$']
  });
});
[1, 2, 6].forEach(function (a) {
  [1, 3, 4, 9].forEach(function (b) {
    add('medium', '치환적분', C(a, 1, 'x/(x^2+' + b + ')'), C(a, 2, 'ln(x^2+' + b + ')'), {
      domain: [0.1, 2.6],
      hints: ['분모의 도함수가 $2x$ 다.', '$\\int\\dfrac{f\'}{f}dx=\\ln|f|$ 를 쓴다.'],
      steps: ['$u=x^{2}+' + b + ',\\;du=2x\\,dx$',
              '$= ' + M.latexOf(C(a, 2, 'ln(x^2+' + b + ')')) + '$']
    });
  });
});
[3, 4].forEach(function (n) {
  [1, 2].forEach(function (a) {
    add('medium', '치환적분', 'x^' + (n - 1) + '/(x^' + n + '+' + a + ')', C(1, n, 'ln(x^' + n + '+' + a + ')'), {
      domain: [0.1, 2.2],
      hints: ['$u=x^{' + n + '}+' + a + '$ 로 둔다.', '$du=' + n + 'x^{' + (n - 1) + '}dx$ 이므로 $' + n + '$ 로 나눈다.'],
      steps: ['$u=x^{' + n + '}+' + a + '$', '$\\dfrac{1}{' + n + '}\\int\\dfrac{du}{u} = ' +
              M.latexOf(C(1, n, 'ln(x^' + n + '+' + a + ')')) + '$']
    });
  });
});

// 부분적분 (다항식 × 초월함수)
[1, 2, 3, -1].forEach(function (k) {
  var byParts = C(1, k * k, '(' + K(k) + ' - 1)*e^(' + K(k) + ')');
  add('medium', '부분적분', 'x*e^(' + K(k) + ')', byParts, {
    domain: D.all,
    hints: ['$u=x,\\;dv=e^{' + K(k) + '}dx$ 로 둔다.', '$\\int u\\,dv=uv-\\int v\\,du$'],
    steps: ['$u=x,\\;v=' + FR('e^{' + K(k) + '}', k) + '$',
            '$' + FR('xe^{' + K(k) + '}', k) + '-' + FR('1', k) + '\\int e^{' + K(k) + '}dx$',
            '$= ' + M.latexOf(byParts) + '$']
  });
});
[1, 2, 3].forEach(function (k) {
  add('medium', '부분적분', 'x*sin(' + K(k) + ')', S(C(-1, k, 'x*cos(' + K(k) + ')'), C(1, k * k, 'sin(' + K(k) + ')')), {
    domain: D.trigW,
    hints: ['$u=x$ 로 두어 차수를 낮춘다.', '$v=' + M.latexOf(C(-1, k, 'cos(' + K(k) + ')')) + '$'],
    steps: ['$u=x,\\;dv=\\sin ' + K(k) + '\\,dx$',
            '$= ' + M.latexOf(S(C(-1, k, 'x*cos(' + K(k) + ')'), C(1, k * k, 'sin(' + K(k) + ')'))) + '$']
  });
  add('medium', '부분적분', 'x*cos(' + K(k) + ')', S(C(1, k, 'x*sin(' + K(k) + ')'), C(1, k * k, 'cos(' + K(k) + ')')), {
    domain: D.trigW,
    hints: ['$u=x,\\;dv=\\cos ' + K(k) + '\\,dx$', '남는 적분은 $\\int\\sin$ 이다.'],
    steps: ['$u=x,\\;v=' + M.latexOf(C(1, k, 'sin(' + K(k) + ')')) + '$',
            '$= ' + M.latexOf(S(C(1, k, 'x*sin(' + K(k) + ')'), C(1, k * k, 'cos(' + K(k) + ')'))) + '$']
  });
});
[1, 2, 3, 4].forEach(function (n) {
  add('medium', '부분적분', 'x^' + n + '*ln(x)',
      S(C(1, n + 1, 'x^' + (n + 1) + '*ln(x)'), C(-1, (n + 1) * (n + 1), 'x^' + (n + 1))), {
    domain: D.pos,
    hints: ['$u=\\ln x,\\;dv=x^{' + n + '}dx$ 로 둔다.', '남는 적분은 $\\int\\dfrac{x^{' + n + '}}{' + (n + 1) + '}dx$ 다.'],
    steps: ['$u=\\ln x,\\;v=\\dfrac{x^{' + (n + 1) + '}}{' + (n + 1) + '}$',
            '$= ' + M.latexOf(S(C(1, n + 1, 'x^' + (n + 1) + '*ln(x)'), C(-1, (n + 1) * (n + 1), 'x^' + (n + 1)))) + '$']
  });
});
[1, 2, 3].forEach(function (a) {
  add('medium', '부분적분', 'ln(' + K(a) + ')', 'x*ln(' + K(a) + ')-x', {
    domain: D.pos,
    hints: ['$dv=dx$ 로 두는 고전적인 수법이다.', '$u=\\ln ' + K(a) + ',\\;du=\\dfrac{dx}{x}$'],
    steps: ['$u=\\ln ' + K(a) + ',\\;dv=dx$', '$x\\ln ' + K(a) + '-\\int x\\cdot\\dfrac{1}{x}dx = x\\ln ' + K(a) + '-x$']
  });
});
[1, 2].forEach(function (a) {
  add('medium', '부분적분', 'atan(' + K(a) + ')', S('x*atan(' + K(a) + ')', C(-1, 2 * a, 'ln(1+' + (a * a) + 'x^2)')), {
    domain: [0.1, 2.2],
    hints: ['$dv=dx$ 로 두고 부분적분한다.', '$du=\\dfrac{' + a + '}{1+' + (a * a) + 'x^{2}}dx$'],
    steps: ['$u=\\arctan ' + K(a) + ',\\;dv=dx$',
            '$= ' + M.latexOf(S('x*atan(' + K(a) + ')', C(-1, 2 * a, 'ln(1+' + (a * a) + 'x^2)'))) + '$']
  });
  add('medium', '부분적분', 'asin(' + K(a) + ')', S('x*asin(' + K(a) + ')', C(1, a, 'sqrt(1-' + (a * a) + 'x^2)')), {
    domain: [-0.6 / a, 0.6 / a],
    hints: ['$dv=dx$ 로 두고 부분적분한다.', '남는 적분은 $u$ 치환으로 근호가 나온다.'],
    steps: ['$u=\\arcsin ' + K(a) + ',\\;dv=dx$',
            '$= ' + M.latexOf(S('x*asin(' + K(a) + ')', C(1, a, 'sqrt(1-' + (a * a) + 'x^2)'))) + '$']
  });
});

// 반각공식
[1, 2, 3].forEach(function (k) {
  add('medium', '반각공식', 'sin(' + K(k) + ')^2', S('x/2', C(-1, 4 * k, 'sin(' + K(2 * k) + ')')), {
    domain: D.trigW,
    hints: ['$\\sin^{2}\\theta=\\dfrac{1-\\cos 2\\theta}{2}$ 로 차수를 낮춘다.', '안쪽 각이 $' + K(2 * k) + '$ 가 된다.'],
    steps: ['$\\sin^{2}' + K(k) + ' = \\dfrac{1-\\cos ' + K(2 * k) + '}{2}$',
            '$\\int = ' + M.latexOf(S('x/2', C(-1, 4 * k, 'sin(' + K(2 * k) + ')'))) + '$']
  });
  add('medium', '반각공식', 'cos(' + K(k) + ')^2', S('x/2', C(1, 4 * k, 'sin(' + K(2 * k) + ')')), {
    domain: D.trigW,
    hints: ['$\\cos^{2}\\theta=\\dfrac{1+\\cos 2\\theta}{2}$ 를 쓴다.', '부호가 $\\sin^{2}$ 일 때와 반대다.'],
    steps: ['$\\cos^{2}' + K(k) + ' = \\dfrac{1+\\cos ' + K(2 * k) + '}{2}$',
            '$\\int = ' + M.latexOf(S('x/2', C(1, 4 * k, 'sin(' + K(2 * k) + ')'))) + '$']
  });
});

// tan / cot / sec / csc
[1, 2, 3].forEach(function (k) {
  add('medium', '삼각함수', 'tan(' + K(k) + ')', C(-1, k, 'ln(cos(' + K(k) + '))'), {
    domain: dTrig(k), lnAbs: true,
    hints: ['$\\tan u=\\dfrac{\\sin u}{\\cos u}$ 로 쓴다.', '$u=\\cos ' + K(k) + '$ 로 치환한다.'],
    steps: ['$u=\\cos ' + K(k) + ',\\;du=-' + KC(k) + '\\sin ' + K(k) + '\\,dx$',
            '$= ' + M.latexOf(C(-1, k, 'ln(cos(' + K(k) + '))'), { lnAbs: true }) + '$']
  });
  add('medium', '삼각함수', 'cot(' + K(k) + ')', C(1, k, 'ln(sin(' + K(k) + '))'), {
    domain: dCot(k), lnAbs: true,
    hints: ['$\\cot u=\\dfrac{\\cos u}{\\sin u}$ 다.', '$u=\\sin ' + K(k) + '$ 로 치환한다.'],
    steps: ['$u=\\sin ' + K(k) + '$', '$= ' + M.latexOf(C(1, k, 'ln(sin(' + K(k) + '))'), { lnAbs: true }) + '$']
  });
  add('medium', '고전 기법', 'sec(' + K(k) + ')', C(1, k, 'ln(sec(' + K(k) + ')+tan(' + K(k) + '))'), {
    domain: dTrig(k), lnAbs: true,
    hints: ['$\\dfrac{\\sec u+\\tan u}{\\sec u+\\tan u}$ 를 곱한다.', '분자가 분모의 도함수가 된다.'],
    steps: ['$\\sec u\\cdot\\dfrac{\\sec u+\\tan u}{\\sec u+\\tan u}$',
            '$= ' + M.latexOf(C(1, k, 'ln(sec(' + K(k) + ')+tan(' + K(k) + '))'), { lnAbs: true }) + '$']
  });
  add('medium', '고전 기법', 'csc(' + K(k) + ')', C(1, k, 'ln(csc(' + K(k) + ')-cot(' + K(k) + '))'), {
    domain: dCot(k), lnAbs: true,
    hints: ['$\\dfrac{\\csc u-\\cot u}{\\csc u-\\cot u}$ 를 곱한다.', '$\\sec$ 와 같은 요령이다.'],
    steps: ['$u=\\csc ' + K(k) + '-\\cot ' + K(k) + '$',
            '$= ' + M.latexOf(C(1, k, 'ln(csc(' + K(k) + ')-cot(' + K(k) + '))'), { lnAbs: true }) + '$']
  });
});

// 역삼각 적분표 (a 포함)
[1, 2, 3, 4, 5].forEach(function (a) {
  add('medium', '역삼각함수', '1/(x^2+' + (a * a) + ')', C(1, a, 'atan(' + X(a) + ')'), {
    domain: [-2.0, 3.0],
    hints: ['$\\int\\dfrac{dx}{x^{2}+a^{2}}=\\dfrac{1}{a}\\arctan\\dfrac{x}{a}$', '여기서 $a=' + a + '$ 다.'],
    steps: ['$a=' + a + '$', '$= ' + M.latexOf(C(1, a, 'atan(' + X(a) + ')')) + '$']
  });
});
[2, 3, 4, 5].forEach(function (a) {
  add('medium', '역삼각함수', '1/sqrt(' + (a * a) + '-x^2)', 'asin(' + X(a) + ')', {
    domain: [-0.7 * a, 0.7 * a],
    hints: ['$\\int\\dfrac{dx}{\\sqrt{a^{2}-x^{2}}}=\\arcsin\\dfrac{x}{a}$', '여기서 $a=' + a + '$ 다.'],
    steps: ['$a=' + a + '$', '$= \\arcsin' + XL(a) + '$']
  });
});

// 삼각함수 홀수 차수
[1, 2].forEach(function (k) {
  add('medium', '삼각함수 홀수차', 'sin(' + K(k) + ')^3',
      S(C(-1, k, 'cos(' + K(k) + ')'), C(1, 3 * k, 'cos(' + K(k) + ')^3')), {
    domain: D.trigW,
    hints: ['$\\sin^{3}u=\\sin u(1-\\cos^{2}u)$ 로 쪼갠다.', '$u=\\cos ' + K(k) + '$ 로 치환한다.'],
    steps: ['$\\sin^{3}' + K(k) + ' = (1-\\cos^{2}' + K(k) + ')\\sin ' + K(k) + '$',
            '$= ' + M.latexOf(S(C(-1, k, 'cos(' + K(k) + ')'), C(1, 3 * k, 'cos(' + K(k) + ')^3'))) + '$']
  });
  add('medium', '삼각함수 홀수차', 'cos(' + K(k) + ')^3',
      S(C(1, k, 'sin(' + K(k) + ')'), C(-1, 3 * k, 'sin(' + K(k) + ')^3')), {
    domain: D.trigW,
    hints: ['$\\cos^{3}u=\\cos u(1-\\sin^{2}u)$ 로 쪼갠다.', '$u=\\sin ' + K(k) + '$ 로 치환한다.'],
    steps: ['$\\cos^{3}' + K(k) + ' = (1-\\sin^{2}' + K(k) + ')\\cos ' + K(k) + '$',
            '$= ' + M.latexOf(S(C(1, k, 'sin(' + K(k) + ')'), C(-1, 3 * k, 'sin(' + K(k) + ')^3'))) + '$']
  });
});

// 근호 치환
[1, 2].forEach(function (a) {
  [1, 3].forEach(function (b) {
    var u = '(' + K(a) + '+' + b + ')';
    add('medium', '치환적분', 'x*sqrt' + u,
        S(C(2, 5 * a * a, u + '^(5/2)'), C(-2 * b, 3 * a * a, u + '^(3/2)')), {
      domain: [0.1, 2.6],
      hints: ['$u=' + K(a) + '+' + b + '$ 로 두면 $x=\\dfrac{u-' + b + '}{' + a + '}$ 다.',
              '$(u-' + b + ')\\sqrt{u}$ 를 전개해 항별로 적분한다.'],
      steps: ['$u=' + K(a) + '+' + b + '$',
              '$\\int (u^{3/2}-' + b + 'u^{1/2})\\dfrac{du}{' + (a * a) + '}$',
              '$= ' + M.latexOf(S(C(2, 5 * a * a, u + '^(5/2)'), C(-2 * b, 3 * a * a, u + '^(3/2)'))) + '$']
    });
  });
  [1, 3, 4].forEach(function (b) {
    add('medium', '치환적분', 'x/sqrt(x^2+' + b + ')', 'sqrt(x^2+' + b + ')', {
      domain: [0.1, 2.8],
      hints: ['$u=x^{2}+' + b + '$ 로 둔다.', '$\\int u^{-1/2}du=2\\sqrt{u}$ 를 기억한다.'],
      steps: ['$u=x^{2}+' + b + ',\\;du=2x\\,dx$', '$\\dfrac{1}{2}\\int u^{-1/2}du=\\sqrt{x^{2}+' + b + '}$']
    });
  });
  [1, 2, 3].forEach(function (b) {
    add('medium', '치환적분', 'sqrt(' + K(a) + '+' + b + ')', C(2, 3 * a, '(' + K(a) + '+' + b + ')^(3/2)'), {
      domain: [0.1, 2.6],
      hints: ['$u=' + K(a) + '+' + b + '$ 로 두면 $du=' + KC(a) + '\\,dx$ 다.', '$\\int u^{1/2}du=\\dfrac{2}{3}u^{3/2}$'],
      steps: ['$u=' + K(a) + '+' + b + '$',
              '$= ' + M.latexOf(C(2, 3 * a, '(' + K(a) + '+' + b + ')^(3/2)')) + '$']
    });
  });
});

// 로그 치환
[1, 2, 3].forEach(function (n) {
  add('medium', '치환적분', 'ln(x)^' + n + '/x', C(1, n + 1, 'ln(x)^' + (n + 1)), {
    domain: [0.4, 4.0],
    hints: ['$u=\\ln x$ 로 두면 $du=\\dfrac{dx}{x}$ 다.', '남는 것은 $\\int u^{' + n + '}du$ 다.'],
    steps: ['$u=\\ln x$', '$\\int u^{' + n + '}du = ' + M.latexOf(C(1, n + 1, 'ln(x)^' + (n + 1))) + '$']
  });
});
add('medium', '이중 치환', '1/(x*ln(x))', 'ln(ln(x))', {
  domain: D.lnln, lnAbs: true,
  hints: ['$u=\\ln x$ 로 두면 적분이 $\\int\\dfrac{du}{u}$ 가 된다.', '로그가 두 번 겹친다.'],
  steps: ['$u=\\ln x,\\;du=\\dfrac{dx}{x}$', '$\\int\\dfrac{du}{u}=\\ln|\\ln x|$']
});

// 부분분수 (서로 다른 1차 인수)
[[1, 2, 3, 5], [1, 3, 2, 4], [2, 3, 1, 1], [1, 4, 5, 2], [2, 5, 3, -1],
 [1, 2, 4, 7], [3, 4, 2, 5], [1, 5, 2, 3]].forEach(function (q) {
  var a = q[0], b = q[1], pp = q[2], qq = q[3];      // (pp x + qq)/((x+a)(x+b))
  var An = qq - pp * a, Ad = b - a;
  var Bn = qq - pp * b, Bd = a - b;
  var integ = '(' + K(pp) + (qq < 0 ? ' - ' + (-qq) : ' + ' + qq) + ')/((x+' + a + ')(x+' + b + '))';
  var ans = S(C(An, Ad, 'ln(x+' + a + ')'), C(Bn, Bd, 'ln(x+' + b + ')'));
  add('medium', '부분분수', integ, ans, {
    domain: [0.2, 3.0], lnAbs: true,
    hints: ['$\\dfrac{A}{x+' + a + '}+\\dfrac{B}{x+' + b + '}$ 로 분해한다.',
            '$x=-' + a + ',\\;x=-' + b + '$ 를 대입하면 $A,B$ 가 바로 나온다.'],
    steps: ['$' + M.latexOf(K(pp) + (qq < 0 ? qq : '+' + qq)) + ' = A(x+' + b + ')+B(x+' + a + ')$',
            '$A=' + M.latexOf(C(An, Ad)) + ',\\;B=' + M.latexOf(C(Bn, Bd)) + '$',
            '$= ' + M.latexOf(ans, { lnAbs: true }) + '$']
  });
});

// f'/f 꼴
[[1, 3, 5], [2, 1, 4], [3, 2, 6], [1, -1, 3], [4, 5, 9]].forEach(function (q) {
  var b = q[1], c = q[2];
  var integ = '(2x' + (b < 0 ? ' - ' + (-b) : ' + ' + b) + ')/(x^2' + (b < 0 ? ' - ' + (-b) : ' + ' + b) + 'x + ' + c + ')';
  add('medium', '치환적분', integ, 'ln(x^2' + (b < 0 ? '-' + (-b) : '+' + b) + 'x+' + c + ')', {
    domain: [0.2, 2.6], lnAbs: true,
    hints: ['분자가 분모의 도함수와 정확히 같다.', '$\\int\\dfrac{f\'}{f}dx=\\ln|f|$'],
    steps: ['$u=x^{2}' + (b < 0 ? b : '+' + b) + 'x+' + c + '$', '$\\int\\dfrac{du}{u}=\\ln|u|$']
  });
});

// 합성 치환
add('medium', '치환적분', 'cos(x)/(1+sin(x)^2)', 'atan(sin(x))', {
  domain: [0.1, 1.4],
  hints: ['$u=\\sin x$ 로 두면 $du=\\cos x\\,dx$ 다.', '남은 적분이 $\\arctan$ 꼴이다.'],
  steps: ['$u=\\sin x$', '$\\int\\dfrac{du}{1+u^{2}}=\\arctan(\\sin x)$']
});
add('medium', '치환적분', 'sin(x)/(1+cos(x)^2)', '-atan(cos(x))', {
  domain: [0.2, 2.8],
  hints: ['$u=\\cos x$ 로 두면 $du=-\\sin x\\,dx$ 다.', '부호에 주의한다.'],
  steps: ['$u=\\cos x$', '$-\\int\\dfrac{du}{1+u^{2}}=-\\arctan(\\cos x)$']
});
add('medium', '치환적분', 'e^x/(1+e^(2x))', 'atan(e^x)', {
  domain: [-1.2, 1.5],
  hints: ['$e^{2x}=(e^{x})^{2}$ 임을 이용한다.', '$u=e^{x}$ 로 치환한다.'],
  steps: ['$u=e^{x},\\;du=e^{x}dx$', '$\\int\\dfrac{du}{1+u^{2}}=\\arctan(e^{x})$']
});
[1, 2, 3].forEach(function (a) {
  add('medium', '치환적분', 'e^x/(e^x+' + a + ')', 'ln(e^x+' + a + ')', {
    domain: [-1.0, 1.8],
    hints: ['분자가 분모의 도함수다.', '$u=e^{x}+' + a + '$ 로 둔다.'],
    steps: ['$u=e^{x}+' + a + '$', '$\\int\\dfrac{du}{u}=\\ln(e^{x}+' + a + ')$']
  });
});

// 순환 부분적분 (기본형)
add('medium', '순환 부분적분', 'e^x*sin(x)', 'e^x*(sin(x)-cos(x))/2', {
  domain: [0.1, 2.5],
  hints: ['부분적분을 두 번 하면 원래 적분 $I$ 가 다시 나온다.', '$I$ 에 대한 방정식을 세워 푼다.'],
  steps: ['$I=\\int e^{x}\\sin x\\,dx$', '$I = e^{x}\\sin x-e^{x}\\cos x-I$', '$2I=e^{x}(\\sin x-\\cos x)$']
});
add('medium', '순환 부분적분', 'e^x*cos(x)', 'e^x*(sin(x)+cos(x))/2', {
  domain: [0.1, 2.5],
  hints: ['$\\sin$ 일 때와 같은 방법이다.', '두 번 부분적분 후 $I$ 를 정리한다.'],
  steps: ['$I=\\int e^{x}\\cos x\\,dx$', '$2I=e^{x}(\\sin x+\\cos x)$']
});
add('medium', '반복 부분적분', 'x^2*e^x', '(x^2-2x+2)*e^x', {
  domain: D.all,
  hints: ['부분적분을 두 번 적용해 차수를 내린다.', '중간에 $\\int xe^{x}dx$ 가 나온다.'],
  steps: ['$x^{2}e^{x}-2\\int xe^{x}dx$', '$\\int xe^{x}dx=(x-1)e^{x}$', '$=(x^{2}-2x+2)e^{x}$']
});

// 쌍곡선함수 (보통)
[1, 2, 3].forEach(function (k) {
  add('medium', '쌍곡선함수', 'tanh(' + K(k) + ')', C(1, k, 'ln(cosh(' + K(k) + '))'), {
    domain: D.hyp,
    hints: ['$\\tanh u=\\dfrac{\\sinh u}{\\cosh u}$ 다.', '$\\cosh$ 는 항상 양수라 절댓값이 필요 없다.'],
    steps: ['$u=\\cosh ' + K(k) + ',\\;du=' + KC(k) + '\\sinh ' + K(k) + '\\,dx$',
            '$= ' + M.latexOf(C(1, k, 'ln(cosh(' + K(k) + '))')) + '$']
  });
  add('medium', '쌍곡선함수', 'coth(' + K(k) + ')', C(1, k, 'ln(sinh(' + K(k) + '))'), {
    domain: D.hypP, lnAbs: true,
    hints: ['$\\coth u=\\dfrac{\\cosh u}{\\sinh u}$ 다.', '$u=\\sinh ' + K(k) + '$ 로 치환한다.'],
    steps: ['$u=\\sinh ' + K(k) + '$', '$= ' + M.latexOf(C(1, k, 'ln(sinh(' + K(k) + '))'), { lnAbs: true }) + '$']
  });
  add('medium', '쌍곡선 항등식', 'sinh(' + K(k) + ')^2', S(C(1, 4 * k, 'sinh(' + K(2 * k) + ')'), '-x/2'), {
    domain: D.hyp,
    hints: ['$\\sinh^{2}u=\\dfrac{\\cosh 2u-1}{2}$ 를 쓴다.', '삼각함수의 반각공식과 부호가 다르다.'],
    steps: ['$\\sinh^{2}' + K(k) + ' = \\dfrac{\\cosh ' + K(2 * k) + '-1}{2}$',
            '$\\int = ' + M.latexOf(S(C(1, 4 * k, 'sinh(' + K(2 * k) + ')'), '-x/2')) + '$']
  });
  add('medium', '쌍곡선 항등식', 'cosh(' + K(k) + ')^2', S(C(1, 4 * k, 'sinh(' + K(2 * k) + ')'), 'x/2'), {
    domain: D.hyp,
    hints: ['$\\cosh^{2}u=\\dfrac{\\cosh 2u+1}{2}$ 를 쓴다.', '$\\sinh^{2}$ 일 때와 부호만 다르다.'],
    steps: ['$\\cosh^{2}' + K(k) + ' = \\dfrac{\\cosh ' + K(2 * k) + '+1}{2}$',
            '$\\int = ' + M.latexOf(S(C(1, 4 * k, 'sinh(' + K(2 * k) + ')'), 'x/2')) + '$']
  });
  add('medium', '쌍곡선 항등식', 'tanh(' + K(k) + ')^2', S('x', C(-1, k, 'tanh(' + K(k) + ')')), {
    domain: D.hyp,
    hints: ['$\\tanh^{2}u=1-\\operatorname{sech}^{2}u$ 다.', '삼각함수의 $\\tan^{2}$ 와 부호가 반대다.'],
    steps: ['$\\tanh^{2}' + K(k) + ' = 1-\\operatorname{sech}^{2}' + K(k) + '$',
            '$\\int = ' + M.latexOf(S('x', C(-1, k, 'tanh(' + K(k) + ')'))) + '$']
  });
  add('medium', '쌍곡선함수', 'sinh(' + K(k) + ')cosh(' + K(k) + ')', C(1, 4 * k, 'cosh(' + K(2 * k) + ')'), {
    domain: D.hyp,
    hints: ['$\\sinh 2u=2\\sinh u\\cosh u$ 를 쓰거나 $u=\\sinh$ 로 치환한다.', '둘 중 어느 쪽이든 상수 차이만 난다.'],
    steps: ['$\\sinh ' + K(k) + '\\cosh ' + K(k) + ' = \\dfrac{\\sinh ' + K(2 * k) + '}{2}$',
            '$= ' + M.latexOf(C(1, 4 * k, 'cosh(' + K(2 * k) + ')')) + '$']
  });
  add('medium', '쌍곡선함수', 'sech(' + K(k) + ')^2*tanh(' + K(k) + ')', C(1, 2 * k, 'tanh(' + K(k) + ')^2'), {
    domain: D.hyp,
    hints: ['$u=\\tanh ' + K(k) + '$ 로 두면 $du=' + KC(k) + '\\operatorname{sech}^{2}' + K(k) + 'dx$ 다.', '남는 것은 $\\int u\\,du$ 다.'],
    steps: ['$u=\\tanh ' + K(k) + '$', '$= ' + M.latexOf(C(1, 2 * k, 'tanh(' + K(k) + ')^2')) + '$']
  });
});
[1, 2, 3].forEach(function (a) {
  add('medium', '역쌍곡선함수', '1/sqrt(x^2+' + (a * a) + ')', 'asinh(' + X(a) + ')', {
    domain: [-1.5, 2.5],
    hints: ['$\\int\\dfrac{dx}{\\sqrt{x^{2}+a^{2}}}=\\operatorname{arsinh}\\dfrac{x}{a}$', '$x=' + KL(a, '\\sinh\\theta') + '$ 로 치환해도 된다.'],
    steps: ['$x=' + KL(a, '\\sinh\\theta') + '$', '$= \\operatorname{arsinh}' + XL(a) + '$']
  });
  add('medium', '역쌍곡선함수', '1/sqrt(x^2-' + (a * a) + ')', 'acosh(' + X(a) + ')', {
    domain: [a * 1.25, a * 3.2],
    hints: ['$\\int\\dfrac{dx}{\\sqrt{x^{2}-a^{2}}}=\\operatorname{arcosh}\\dfrac{x}{a}$', '$x=' + KL(a, '\\cosh\\theta') + '$ 로 치환한다.'],
    steps: ['$x=' + KL(a, '\\cosh\\theta') + '$', '$= \\operatorname{arcosh}' + XL(a) + '$']
  });
  add('medium', '역쌍곡선함수', '1/(' + (a * a) + '-x^2)', C(1, a, 'atanh(' + X(a) + ')'), {
    domain: [-0.7 * a, 0.7 * a],
    hints: ['$|x|<' + a + '$ 에서 $\\int\\dfrac{dx}{a^{2}-x^{2}}=\\dfrac{1}{a}\\operatorname{artanh}\\dfrac{x}{a}$',
            '부분분수로 풀면 로그 형태로도 쓸 수 있다.'],
    steps: ['$\\dfrac{1}{' + (a * a) + '-x^{2}}$ 를 부분분수로 분해',
            '$= ' + M.latexOf(C(1, a, 'atanh(' + X(a) + ')')) + '$']
  });
});
[1, 2].forEach(function (k) {
  add('medium', '부분적분', 'x*sinh(' + K(k) + ')', S(C(1, k, 'x*cosh(' + K(k) + ')'), C(-1, k * k, 'sinh(' + K(k) + ')')), {
    domain: D.hyp,
    hints: ['$u=x,\\;dv=\\sinh ' + K(k) + '\\,dx$ 로 둔다.', '삼각함수와 달리 부호가 바뀌지 않는다.'],
    steps: ['$u=x,\\;v=' + M.latexOf(C(1, k, 'cosh(' + K(k) + ')')) + '$',
            '$= ' + M.latexOf(S(C(1, k, 'x*cosh(' + K(k) + ')'), C(-1, k * k, 'sinh(' + K(k) + ')'))) + '$']
  });
  add('medium', '부분적분', 'x*cosh(' + K(k) + ')', S(C(1, k, 'x*sinh(' + K(k) + ')'), C(-1, k * k, 'cosh(' + K(k) + ')')), {
    domain: D.hyp,
    hints: ['$u=x,\\;dv=\\cosh ' + K(k) + '\\,dx$ 로 둔다.', '남는 적분은 $\\int\\sinh$ 다.'],
    steps: ['$u=x,\\;v=' + M.latexOf(C(1, k, 'sinh(' + K(k) + ')')) + '$',
            '$= ' + M.latexOf(S(C(1, k, 'x*sinh(' + K(k) + ')'), C(-1, k * k, 'cosh(' + K(k) + ')'))) + '$']
  });
});

// ================================================================== 어려움

// 부호를 붙여 항을 잇는 헬퍼 (a>=0 이면 '+a')
function sg(v) { return v < 0 ? ' - ' + (-v) : ' + ' + v; }

// 삼각치환
[1, 2, 3].forEach(function (a) {
  var a2 = a * a;
  add('medium', '삼각치환', 'sqrt(' + a2 + '-x^2)',
      S(C(1, 2, 'x*sqrt(' + a2 + '-x^2)'), C(a2, 2, 'asin(' + X(a) + ')')), {
    domain: [-0.75 * a, 0.75 * a],
    hints: ['$x=' + KL(a, '\\sin\\theta') + '$ 로 치환한다.', '$\\cos^{2}\\theta$ 는 반각공식으로 처리한다.'],
    steps: ['$x=' + KL(a, '\\sin\\theta') + ',\\;dx=' + KL(a, '\\cos\\theta') + '\\,d\\theta$',
            '$' + KL(a2, '\\int') + '\\cos^{2}\\theta\\,d\\theta = ' + KL(a2, '\\left(\\dfrac{\\theta}{2}+\\dfrac{\\sin 2\\theta}{4}\\right)') + '$',
            '$= ' + M.latexOf(S(C(1, 2, 'x*sqrt(' + a2 + '-x^2)'), C(a2, 2, 'asin(' + X(a) + ')'))) + '$']
  });
  add('medium', '쌍곡선 치환', 'sqrt(x^2+' + a2 + ')',
      S(C(1, 2, 'x*sqrt(x^2+' + a2 + ')'), C(a2, 2, 'asinh(' + X(a) + ')')), {
    domain: [-1.4, 2.4],
    hints: ['$x=' + KL(a, '\\sinh\\theta') + '$ 로 치환하면 근호가 $\\cosh$ 로 풀린다.',
            '$\\cosh^{2}\\theta=\\dfrac{\\cosh 2\\theta+1}{2}$ 를 쓴다.'],
    steps: ['$x=' + KL(a, '\\sinh\\theta') + '$', '$' + KL(a2, '\\int') + '\\cosh^{2}\\theta\\,d\\theta$',
            '$= ' + M.latexOf(S(C(1, 2, 'x*sqrt(x^2+' + a2 + ')'), C(a2, 2, 'asinh(' + X(a) + ')'))) + '$']
  });
  add('medium', '쌍곡선 치환', 'sqrt(x^2-' + a2 + ')',
      S(C(1, 2, 'x*sqrt(x^2-' + a2 + ')'), C(-a2, 2, 'acosh(' + X(a) + ')')), {
    domain: [a * 1.3, a * 3.0],
    hints: ['$x=' + KL(a, '\\cosh\\theta') + '$ 로 치환한다.', '$\\sinh^{2}\\theta=\\dfrac{\\cosh 2\\theta-1}{2}$'],
    steps: ['$x=' + KL(a, '\\cosh\\theta') + '$', '$' + KL(a2, '\\int') + '\\sinh^{2}\\theta\\,d\\theta$',
            '$= ' + M.latexOf(S(C(1, 2, 'x*sqrt(x^2-' + a2 + ')'), C(-a2, 2, 'acosh(' + X(a) + ')'))) + '$']
  });
  add('medium', '삼각치환', 'x^2/sqrt(' + a2 + '-x^2)',
      S(C(a2, 2, 'asin(' + X(a) + ')'), C(-1, 2, 'x*sqrt(' + a2 + '-x^2)')), {
    domain: [-0.75 * a, 0.75 * a],
    hints: ['$x=' + KL(a, '\\sin\\theta') + '$ 로 두면 $\\int\\sin^{2}\\theta\\,d\\theta$ 가 된다.', '반각공식 후 다시 $x$ 로 되돌린다.'],
    steps: ['$x=' + KL(a, '\\sin\\theta') + '$', '$' + KL(a2, '\\int') + '\\sin^{2}\\theta\\,d\\theta$',
            '$= ' + M.latexOf(S(C(a2, 2, 'asin(' + X(a) + ')'), C(-1, 2, 'x*sqrt(' + a2 + '-x^2)'))) + '$']
  });
  add('medium', '삼각치환', '1/(x^2*sqrt(x^2-' + a2 + '))', C(1, a2, 'sqrt(x^2-' + a2 + ')/x'), {
    domain: [a * 1.3, a * 3.4],
    hints: ['$x=' + KL(a, '\\sec\\theta') + '$ 로 치환한다.', '적분이 $\\int\\cos\\theta\\,d\\theta$ 로 줄어든다.'],
    steps: ['$x=' + KL(a, '\\sec\\theta') + '$',
            '$' + FR('1', a2) + '\\int\\cos\\theta\\,d\\theta=' + FR('\\sin\\theta', a2) + '$',
            '$= ' + M.latexOf(C(1, a2, 'sqrt(x^2-' + a2 + ')/x')) + '$']
  });
  add('medium', '삼각치환', '1/(x^2*sqrt(' + a2 + '-x^2))', C(-1, a2, 'sqrt(' + a2 + '-x^2)/x'), {
    domain: [0.35 * a, 0.8 * a],
    hints: ['$x=' + KL(a, '\\sin\\theta') + '$ 로 치환한다.', '$\\int\\csc^{2}\\theta\\,d\\theta=-\\cot\\theta$'],
    steps: ['$x=' + KL(a, '\\sin\\theta') + '$', '$\\dfrac{1}{' + a2 + '}\\int\\csc^{2}\\theta\\,d\\theta$',
            '$= ' + M.latexOf(C(-1, a2, 'sqrt(' + a2 + '-x^2)/x')) + '$']
  });
});

// 완전제곱 (b 는 짝수, d=c-(b/2)^2 은 완전제곱수)
[[2, 5, 2], [4, 13, 3], [2, 2, 1], [6, 13, 2], [-2, 5, 2], [4, 5, 1], [-4, 13, 3], [2, 10, 3], [-6, 13, 2]]
.forEach(function (q) {
  var b = q[0], c = q[1], sd = q[2], h = b / 2;
  var den = '(x^2' + sg(b) + 'x' + sg(c) + ')';
  var shift = '(x' + sg(h) + ')';
  add('medium', '완전제곱', '1/' + den, C(1, sd, 'atan(' + shift + '/' + sd + ')'), {
    domain: [-1.0, 2.6],
    hints: ['분모를 $\\left(x' + (h < 0 ? h : '+' + h) + '\\right)^{2}+' + (sd * sd) + '$ 로 완전제곱한다.',
            '$\\int\\dfrac{du}{u^{2}+a^{2}}=\\dfrac{1}{a}\\arctan\\dfrac{u}{a}$ 에서 $a=' + sd + '$'],
    steps: ['$x^{2}' + sg(b) + 'x' + sg(c) + ' = \\left(x' + (h < 0 ? h : '+' + h) + '\\right)^{2}+' + (sd * sd) + '$',
            '$= ' + M.latexOf(C(1, sd, 'atan(' + shift + '/' + sd + ')')) + '$']
  });
  add('medium', '완전제곱', '1/sqrt' + den, 'asinh(' + shift + '/' + sd + ')', {
    domain: [-1.0, 2.6],
    hints: ['분모 안을 완전제곱하면 $u^{2}+' + (sd * sd) + '$ 꼴이 된다.',
            '$\\int\\dfrac{du}{\\sqrt{u^{2}+a^{2}}}=\\operatorname{arsinh}\\dfrac{u}{a}$'],
    steps: ['$x^{2}' + sg(b) + 'x' + sg(c) + ' = \\left(x' + (h < 0 ? h : '+' + h) + '\\right)^{2}+' + (sd * sd) + '$',
            '$= \\operatorname{arsinh}\\dfrac{x' + (h < 0 ? h : '+' + h) + '}{' + sd + '}$']
  });
});
[[1, 3, 2, 5, 2], [2, 1, 4, 13, 3], [3, 2, 2, 2, 1], [1, 5, 6, 13, 2], [2, -1, -2, 5, 2], [4, 3, 4, 5, 1]]
.forEach(function (q) {
  var pp = q[0], qq = q[1], b = q[2], c = q[3], sd = q[4], h = b / 2;
  var den = '(x^2' + sg(b) + 'x' + sg(c) + ')';
  var shift = '(x' + sg(h) + ')';
  var rest = qq - pp * h;                       // 1차항을 제거하고 남는 상수
  var ans = S(C(pp, 2, 'ln' + den), C(rest, sd, 'atan(' + shift + '/' + sd + ')'));
  add('medium', '완전제곱', '(' + K(pp) + sg(qq) + ')/' + den, ans, {
    domain: [-1.0, 2.6],
    hints: ['분자를 분모의 도함수 $2x' + sg(b) + '$ 의 상수배 + 나머지 상수로 쪼갠다.',
            '앞쪽은 로그, 뒤쪽은 $\\arctan$ 이 된다.'],
    steps: ['$' + M.latexOf(K(pp) + sg(qq)) + ' = ' + M.latexOf(C(pp, 2)) + '\\left(2x' + sg(b) + '\\right)' + sg(rest) + '$',
            '$= ' + M.latexOf(ans) + '$']
  });
});

// 삼각함수 고차
[1, 2].forEach(function (k) {
  add('hard', '삼각함수 고급', 'sec(' + K(k) + ')^3',
      C(1, 2 * k, 'sec(' + K(k) + ')tan(' + K(k) + ')') + ' + ' + C(1, 2 * k, 'ln(sec(' + K(k) + ')+tan(' + K(k) + '))'), {
    domain: dTrig(k), lnAbs: true,
    hints: ['$\\sec^{3}u=\\sec u\\cdot\\sec^{2}u$ 로 나눠 부분적분한다.', '$\\int\\sec u\\,du$ 결과가 다시 필요하다.'],
    steps: ['$u=\\sec ' + K(k) + ',\\;dv=\\sec^{2}' + K(k) + 'dx$',
            '$I = \\sec\\tan-\\int\\sec\\tan^{2}$', '$2I=\\sec\\tan+\\ln|\\sec+\\tan|$']
  });
  add('hard', '삼각함수 고급', 'csc(' + K(k) + ')^3',
      C(-1, 2 * k, 'csc(' + K(k) + ')cot(' + K(k) + ')') + ' + ' + C(1, 2 * k, 'ln(csc(' + K(k) + ')-cot(' + K(k) + '))'), {
    domain: dCot(k), lnAbs: true,
    hints: ['$\\sec^{3}$ 와 같은 방식으로 부분적분한다.', '$\\int\\csc u\\,du$ 가 다시 나온다.'],
    steps: ['$I=\\int\\csc^{3}$', '$2I=-\\csc\\cot+\\ln|\\csc-\\cot|$']
  });
  add('medium', '삼각함수 홀수차', 'tan(' + K(k) + ')^3',
      S(C(1, 2 * k, 'tan(' + K(k) + ')^2'), C(1, k, 'ln(cos(' + K(k) + '))')), {
    domain: dTrig(k), lnAbs: true,
    hints: ['$\\tan^{3}u=\\tan u(\\sec^{2}u-1)$ 로 쪼갠다.', '첫 항은 $u=\\tan$ 치환이다.'],
    steps: ['$\\tan^{3}' + K(k) + ' = \\tan\\sec^{2}-\\tan$',
            '$= ' + M.latexOf(S(C(1, 2 * k, 'tan(' + K(k) + ')^2'), C(1, k, 'ln(cos(' + K(k) + '))')), { lnAbs: true }) + '$']
  });
  add('medium', '삼각함수 홀수차', 'cot(' + K(k) + ')^3',
      S(C(-1, 2 * k, 'cot(' + K(k) + ')^2'), C(-1, k, 'ln(sin(' + K(k) + '))')), {
    domain: dCot(k), lnAbs: true,
    hints: ['$\\cot^{3}u=\\cot u(\\csc^{2}u-1)$ 로 쪼갠다.', '부호에 특히 주의한다.'],
    steps: ['$\\cot^{3}' + K(k) + ' = \\cot\\csc^{2}-\\cot$',
            '$= ' + M.latexOf(S(C(-1, 2 * k, 'cot(' + K(k) + ')^2'), C(-1, k, 'ln(sin(' + K(k) + '))')), { lnAbs: true }) + '$']
  });
});
add('medium', '삼각함수 고차', 'tan(x)^4', 'tan(x)^3/3-tan(x)+x', {
  domain: D.trig,
  hints: ['$\\tan^{4}=\\tan^{2}(\\sec^{2}-1)$ 로 한 단계씩 내린다.', '마지막에 $\\int\\tan^{2}=\\tan x-x$ 를 쓴다.'],
  steps: ['$\\tan^{4}x=\\tan^{2}x\\sec^{2}x-\\tan^{2}x$', '$= \\dfrac{\\tan^{3}x}{3}-\\tan x+x$']
});
add('medium', '삼각함수 고차', 'sec(x)^4', 'tan(x)+tan(x)^3/3', {
  domain: D.trig,
  hints: ['$\\sec^{4}=\\sec^{2}\\cdot\\sec^{2}=(1+\\tan^{2})\\sec^{2}$', '$u=\\tan x$ 치환이면 끝난다.'],
  steps: ['$\\sec^{4}x=(1+\\tan^{2}x)\\sec^{2}x$', '$u=\\tan x:\\;\\int(1+u^{2})du$']
});
add('medium', '삼각함수 고차', 'cot(x)^4', '-cot(x)^3/3+cot(x)+x', {
  domain: [0.45, 1.4],
  hints: ['$\\cot^{4}=\\cot^{2}(\\csc^{2}-1)$ 로 내린다.', '$\\int\\cot^{2}=-\\cot x-x$ 를 쓴다.'],
  steps: ['$\\cot^{4}x=\\cot^{2}x\\csc^{2}x-\\cot^{2}x$', '$= -\\dfrac{\\cot^{3}x}{3}+\\cot x+x$']
});
add('medium', '삼각함수 고차', 'csc(x)^4', '-cot(x)-cot(x)^3/3', {
  domain: [0.5, 1.4],
  hints: ['$\\csc^{4}=(1+\\cot^{2})\\csc^{2}$', '$u=\\cot x$ 로 치환한다.'],
  steps: ['$\\csc^{4}x=(1+\\cot^{2}x)\\csc^{2}x$', '$u=\\cot x:\\;-\\int(1+u^{2})du$']
});

// 부분분수 (반복 인수 / 2차 인수)
[1, 2, 3].forEach(function (a) {
  add('medium', '부분분수', '1/(x^2*(x+' + a + '))',
      S(C(-1, a, '1/x'), C(-1, a * a, 'ln(x)'), C(1, a * a, 'ln(x+' + a + ')')), {
    domain: [0.4, 3.0], lnAbs: true,
    hints: ['$\\dfrac{A}{x}+\\dfrac{B}{x^{2}}+\\dfrac{D}{x+' + a + '}$ 로 분해한다.',
            '$B$ 는 $x=0$, $D$ 는 $x=-' + a + '$ 대입으로 바로 나온다.'],
    steps: ['$1=Ax(x+' + a + ')+B(x+' + a + ')+Dx^{2}$',
            '$B=' + M.latexOf(C(1, a)) + ',\\;D=' + M.latexOf(C(1, a * a)) + ',\\;A=' + M.latexOf(C(-1, a * a)) + '$',
            '$= ' + M.latexOf(S(C(-1, a, '1/x'), C(-1, a * a, 'ln(x)'), C(1, a * a, 'ln(x+' + a + ')')), { lnAbs: true }) + '$']
  });
  add('medium', '부분분수', '1/(x^3+' + (a * a) + 'x)',
      S(C(1, a * a, 'ln(x)'), C(-1, 2 * a * a, 'ln(x^2+' + (a * a) + ')')), {
    domain: [0.35, 3.0], lnAbs: true,
    hints: ['$x(x^{2}+' + (a * a) + ')$ 로 인수분해한다.',
            '$\\dfrac{1}{' + (a * a) + '}\\left(\\dfrac{1}{x}-\\dfrac{x}{x^{2}+' + (a * a) + '}\\right)$ 가 된다.'],
    steps: ['$\\dfrac{1}{x(x^{2}+' + (a * a) + ')} = \\dfrac{1}{' + (a * a) + '}\\left(\\dfrac{1}{x}-\\dfrac{x}{x^{2}+' + (a * a) + '}\\right)$',
            '$= ' + M.latexOf(S(C(1, a * a, 'ln(x)'), C(-1, 2 * a * a, 'ln(x^2+' + (a * a) + ')')), { lnAbs: true }) + '$']
  });
  add('medium', '부분분수', '1/(x^2-' + (a * a) + ')',
      S(C(1, 2 * a, 'ln(x-' + a + ')'), C(-1, 2 * a, 'ln(x+' + a + ')')), {
    domain: [a * 1.3, a * 3.4], lnAbs: true,
    hints: ['$(x-' + a + ')(x+' + a + ')$ 로 인수분해한다.',
            '$\\dfrac{1}{' + (2 * a) + '}\\left(\\dfrac{1}{x-' + a + '}-\\dfrac{1}{x+' + a + '}\\right)$'],
    steps: ['부분분수 분해',
            '$= ' + M.latexOf(S(C(1, 2 * a, 'ln(x-' + a + ')'), C(-1, 2 * a, 'ln(x+' + a + ')')), { lnAbs: true }) + '$']
  });
});
[[1, 2], [1, 3], [2, 3], [1, 4]].forEach(function (q) {
  var a = q[0], b = q[1], d = b - a;
  add('medium', '부분분수', '1/((x+' + a + ')(x+' + b + ')^2)',
      S(C(1, d * d, 'ln(x+' + a + ')'), C(-1, d * d, 'ln(x+' + b + ')'), C(1, d, '1/(x+' + b + ')')), {
    domain: [0.2, 3.0], lnAbs: true,
    hints: ['중복 인수는 $\\dfrac{B}{x+' + b + '}+\\dfrac{D}{(x+' + b + ')^{2}}$ 두 항이 필요하다.',
            '$x=-' + a + '$ 와 $x=-' + b + '$ 를 대입해 계수를 잡는다.'],
    steps: ['$\\dfrac{A}{x+' + a + '}+\\dfrac{B}{x+' + b + '}+\\dfrac{D}{(x+' + b + ')^{2}}$',
            '$A=' + M.latexOf(C(1, d * d)) + ',\\;B=' + M.latexOf(C(-1, d * d)) + ',\\;D=' + M.latexOf(C(-1, d)) + '$',
            '$= ' + M.latexOf(S(C(1, d * d, 'ln(x+' + a + ')'), C(-1, d * d, 'ln(x+' + b + ')'), C(1, d, '1/(x+' + b + ')')), { lnAbs: true }) + '$']
  });
});

// 반복 부분적분
[1, 2, 3, -1].forEach(function (a) {
  add('medium', '반복 부분적분', 'x^2*e^(' + K(a) + ')',
      'e^(' + K(a) + ')*(' + (a * a) + 'x^2 - ' + (2 * a) + 'x + 2)/' + (a * a * a), {
    domain: D.all,
    hints: ['부분적분을 두 번 해서 $x^{2}\\to x\\to 1$ 로 차수를 내린다.', '$\\int xe^{' + K(a) + '}dx$ 가 중간에 나온다.'],
    steps: ['$' + FR('x^{2}e^{' + K(a) + '}', a) + '-' + FR('2', a) + '\\int xe^{' + K(a) + '}dx$',
            '$= ' + M.latexOf('e^(' + K(a) + ')*(' + (a * a) + 'x^2 - ' + (2 * a) + 'x + 2)/' + (a * a * a)) + '$']
  });
});
[1, 2].forEach(function (a) {
  add('medium', '반복 부분적분', 'x^2*sin(' + K(a) + ')',
      S(C(-1, a, 'x^2*cos(' + K(a) + ')'), C(2, a * a, 'x*sin(' + K(a) + ')'), C(2, a * a * a, 'cos(' + K(a) + ')')), {
    domain: D.trigW,
    hints: ['$u=x^{2}$ 로 두고 부분적분을 두 번 한다.', '중간에 $\\int x\\cos ' + K(a) + 'dx$ 가 나온다.'],
    steps: ['$u=x^{2},\\;dv=\\sin ' + K(a) + 'dx$',
            '$= ' + M.latexOf(S(C(-1, a, 'x^2*cos(' + K(a) + ')'), C(2, a * a, 'x*sin(' + K(a) + ')'), C(2, a * a * a, 'cos(' + K(a) + ')'))) + '$']
  });
  add('medium', '반복 부분적분', 'x^2*cos(' + K(a) + ')',
      S(C(1, a, 'x^2*sin(' + K(a) + ')'), C(2, a * a, 'x*cos(' + K(a) + ')'), C(-2, a * a * a, 'sin(' + K(a) + ')')), {
    domain: D.trigW,
    hints: ['$u=x^{2}$ 로 두고 두 번 부분적분한다.', '$\\sin$ 일 때와 부호 배치가 다르다.'],
    steps: ['$u=x^{2},\\;dv=\\cos ' + K(a) + 'dx$',
            '$= ' + M.latexOf(S(C(1, a, 'x^2*sin(' + K(a) + ')'), C(2, a * a, 'x*cos(' + K(a) + ')'), C(-2, a * a * a, 'sin(' + K(a) + ')'))) + '$']
  });
});
add('medium', '반복 부분적분', 'ln(x)^2', 'x*ln(x)^2-2x*ln(x)+2x', {
  domain: D.pos,
  hints: ['$dv=dx$ 로 두고 부분적분한다.', '남는 적분이 $2\\int\\ln x\\,dx$ 다.'],
  steps: ['$u=(\\ln x)^{2},\\;dv=dx$', '$x(\\ln x)^{2}-2\\int\\ln x\\,dx$', '$=x(\\ln x)^{2}-2x\\ln x+2x$']
});

// 순환 부분적분 (일반 계수)
[[1, 2], [2, 1], [2, 3], [3, 2], [-1, 1], [1, 3]].forEach(function (q) {
  var a = q[0], b = q[1], den = a * a + b * b;
  add('medium', '순환 부분적분', 'e^(' + K(a) + ')sin(' + K(b) + ')',
      'e^(' + K(a) + ')*(' + K(a, 'sin(' + K(b) + ')') + ' - ' + K(b, 'cos(' + K(b) + ')') + ')/' + den, {
    domain: [0.05, 1.6],
    hints: ['부분적분 두 번 뒤 원래 적분 $I$ 가 다시 나온다.',
            '분모는 $' + (a * a) + '+' + (b * b) + '=' + den + '$ 이 된다.'],
    steps: ['$I=\\int e^{' + K(a) + '}\\sin ' + K(b) + '\\,dx$',
            '두 번 부분적분해 $I$ 에 대한 방정식을 세운다',
            '$I = ' + M.latexOf('e^(' + K(a) + ')*(' + K(a, 'sin(' + K(b) + ')') + ' - ' + K(b, 'cos(' + K(b) + ')') + ')/' + den) + '$']
  });
  add('medium', '순환 부분적분', 'e^(' + K(a) + ')cos(' + K(b) + ')',
      'e^(' + K(a) + ')*(' + K(a, 'cos(' + K(b) + ')') + ' + ' + K(b, 'sin(' + K(b) + ')') + ')/' + den, {
    domain: [0.05, 1.6],
    hints: ['$\\sin$ 일 때와 같은 방법이다.', '분모는 똑같이 $' + den + '$ 이다.'],
    steps: ['$I=\\int e^{' + K(a) + '}\\cos ' + K(b) + '\\,dx$',
            '$I = ' + M.latexOf('e^(' + K(a) + ')*(' + K(a, 'cos(' + K(b) + ')') + ' + ' + K(b, 'sin(' + K(b) + ')') + ')/' + den) + '$']
  });
});

// 치환 후 부분적분
add('hard', '치환+부분적분', 'sin(ln(x))', 'x*(sin(ln(x))-cos(ln(x)))/2', {
  domain: [0.3, 4.0],
  hints: ['$t=\\ln x$ 로 두면 $\\int e^{t}\\sin t\\,dt$ 가 된다.', '순환 부분적분 결과를 되돌린다.'],
  steps: ['$t=\\ln x,\\;dx=e^{t}dt$', '$\\int e^{t}\\sin t\\,dt=\\dfrac{e^{t}(\\sin t-\\cos t)}{2}$']
});
add('hard', '치환+부분적분', 'cos(ln(x))', 'x*(sin(ln(x))+cos(ln(x)))/2', {
  domain: [0.3, 4.0],
  hints: ['$t=\\ln x$ 치환 후 $\\int e^{t}\\cos t\\,dt$ 다.', '$\\sin(\\ln x)$ 문제와 짝을 이룬다.'],
  steps: ['$t=\\ln x$', '$\\int e^{t}\\cos t\\,dt=\\dfrac{e^{t}(\\sin t+\\cos t)}{2}$']
});
add('hard', '치환+부분적분', 'e^(sqrt(x))', '2*e^(sqrt(x))*(sqrt(x)-1)', {
  domain: [0.2, 3.0],
  hints: ['$t=\\sqrt{x},\\;dx=2t\\,dt$ 로 치환한다.', '남은 $\\int te^{t}dt$ 는 부분적분이다.'],
  steps: ['$t=\\sqrt{x},\\;dx=2t\\,dt$', '$2\\int te^{t}dt=2(t-1)e^{t}$']
});

// 유리화 치환
add('medium', '유리화 치환', 'sqrt(x)/(1+x)', '2sqrt(x)-2atan(sqrt(x))', {
  domain: [0.2, 4.0],
  hints: ['$t=\\sqrt{x}$ 로 두면 $dx=2t\\,dt$ 다.', '$\\dfrac{t^{2}}{1+t^{2}}=1-\\dfrac{1}{1+t^{2}}$'],
  steps: ['$t=\\sqrt{x}$', '$2\\int\\dfrac{t^{2}}{1+t^{2}}dt=2t-2\\arctan t$']
});
add('medium', '유리화 치환', '1/(1+sqrt(x))', '2sqrt(x)-2ln(1+sqrt(x))', {
  domain: [0.2, 4.0],
  hints: ['$t=\\sqrt{x}$ 로 치환한다.', '$\\dfrac{t}{1+t}=1-\\dfrac{1}{1+t}$ 로 나눈다.'],
  steps: ['$t=\\sqrt{x},\\;dx=2t\\,dt$', '$2\\int\\dfrac{t}{1+t}dt=2t-2\\ln(1+t)$']
});
add('medium', '유리화 치환', '1/(sqrt(x)*(1+x))', '2atan(sqrt(x))', {
  domain: [0.2, 4.0],
  hints: ['$t=\\sqrt{x}$ 로 두면 $\\dfrac{dx}{\\sqrt{x}}=2dt$ 다.', '남는 적분이 곧바로 $\\arctan$ 이다.'],
  steps: ['$t=\\sqrt{x}$', '$2\\int\\dfrac{dt}{1+t^{2}}=2\\arctan\\sqrt{x}$']
});

// 지수 유리식
add('medium', '지수 유리식', '1/(1+e^x)', 'x-ln(1+e^x)', {
  domain: [-1.5, 2.0],
  hints: ['$\\dfrac{1}{1+e^{x}}=1-\\dfrac{e^{x}}{1+e^{x}}$ 로 쪼갠다.', '두 번째 항은 로그다.'],
  steps: ['$\\dfrac{1}{1+e^{x}}=1-\\dfrac{e^{x}}{1+e^{x}}$', '$\\int = x-\\ln(1+e^{x})$']
});
add('medium', '지수 유리식', '1/(e^x+e^(-x))', 'atan(e^x)', {
  domain: [-1.5, 1.8],
  hints: ['분모·분자에 $e^{x}$ 를 곱한다.', '$u=e^{x}$ 로 두면 $\\arctan$ 이 된다.'],
  steps: ['$\\dfrac{e^{x}}{e^{2x}+1}$', '$u=e^{x}:\\;\\int\\dfrac{du}{1+u^{2}}$']
});
add('medium', '지수 유리식', 'e^x/(e^(2x)-1)', 'ln(e^x-1)/2-ln(e^x+1)/2', {
  domain: [0.35, 2.0], lnAbs: true,
  hints: ['$u=e^{x}$ 로 두면 $\\int\\dfrac{du}{u^{2}-1}$ 이다.', '부분분수로 분해한다.'],
  steps: ['$u=e^{x}$', '$\\int\\dfrac{du}{u^{2}-1}=\\dfrac{1}{2}\\ln\\left|\\dfrac{u-1}{u+1}\\right|$']
});

// 역함수 부분적분
add('medium', '부분적분', 'x*atan(x)', '(x^2+1)*atan(x)/2-x/2', {
  domain: [0.1, 2.5],
  hints: ['$v=\\dfrac{x^{2}+1}{2}$ 로 잡으면 계산이 깔끔해진다.', '적분상수를 $v$ 에 넣는 기술이다.'],
  steps: ['$u=\\arctan x,\\;v=\\dfrac{x^{2}+1}{2}$', '$\\dfrac{(x^{2}+1)\\arctan x}{2}-\\int\\dfrac{1}{2}dx$']
});
add('medium', '부분적분', 'x*asin(x)', '(2x^2-1)*asin(x)/4+x*sqrt(1-x^2)/4', {
  domain: D.unit,
  hints: ['$u=\\arcsin x,\\;dv=x\\,dx$ 로 둔다.', '남는 적분에 삼각치환이 필요하다.'],
  steps: ['$u=\\arcsin x,\\;v=\\dfrac{x^{2}}{2}$',
          '$\\dfrac{x^{2}\\arcsin x}{2}-\\dfrac{1}{2}\\int\\dfrac{x^{2}}{\\sqrt{1-x^{2}}}dx$']
});
add('medium', '부분적분', 'asin(x)', 'x*asin(x)+sqrt(1-x^2)', {
  domain: D.unit,
  hints: ['$dv=dx$ 로 두는 유형이다.', '$du=\\dfrac{dx}{\\sqrt{1-x^{2}}}$'],
  steps: ['$u=\\arcsin x,\\;dv=dx$', '$x\\arcsin x-\\int\\dfrac{x}{\\sqrt{1-x^{2}}}dx$']
});
add('medium', '부분적분', 'acos(x)', 'x*acos(x)-sqrt(1-x^2)', {
  domain: D.unit,
  hints: ['$\\arcsin$ 일 때와 부호만 다르다.', '$du=-\\dfrac{dx}{\\sqrt{1-x^{2}}}$'],
  steps: ['$u=\\arccos x,\\;dv=dx$', '$x\\arccos x+\\int\\dfrac{x}{\\sqrt{1-x^{2}}}dx$']
});
[1, 2, 3].forEach(function (a) {
  add('medium', '부분적분', 'ln(x^2+' + (a * a) + ')', 'x*ln(x^2+' + (a * a) + ')-2x+' + (2 * a) + '*atan(' + X(a) + ')', {
    domain: [0.1, 2.5],
    hints: ['$dv=dx$ 로 두고 부분적분한다.',
            '남는 $\\int\\dfrac{2x^{2}}{x^{2}+' + (a * a) + '}dx$ 를 나눗셈으로 정리한다.'],
    steps: ['$u=\\ln(x^{2}+' + (a * a) + '),\\;dv=dx$',
            '$\\dfrac{2x^{2}}{x^{2}+' + (a * a) + '}=2-\\dfrac{' + (2 * a * a) + '}{x^{2}+' + (a * a) + '}$']
  });
});

// 치환 (근호 안 다항식)
[1, 4, 9].forEach(function (a) {
  add('medium', '치환적분', 'x^3/sqrt(x^2+' + a + ')', '(x^2+' + a + ')^(3/2)/3-' + a + '*sqrt(x^2+' + a + ')', {
    domain: [0.1, 2.5],
    hints: ['$u=x^{2}+' + a + '$ 이면 $x^{2}=u-' + a + '$ 다.', '$\\dfrac{1}{2}\\int\\dfrac{u-' + a + '}{\\sqrt{u}}du$ 를 계산한다.'],
    steps: ['$u=x^{2}+' + a + ',\\;du=2x\\,dx$', '$\\dfrac{1}{2}\\int (u^{1/2}-' + a + 'u^{-1/2})du$']
  });
  add('medium', '치환적분', 'x/(x^4+' + (a * a) + ')', C(1, 2 * a, 'atan(x^2/' + a + ')'), {
    domain: [0.1, 2.5],
    hints: ['$x^{4}=(x^{2})^{2}$ 이므로 $u=x^{2}$ 로 둔다.', '$du=2x\\,dx$ 가 분자와 맞는다.'],
    steps: ['$u=x^{2},\\;du=2x\\,dx$', '$\\dfrac{1}{2}\\int\\dfrac{du}{u^{2}+' + (a * a) + '}$']
  });
});

// 쌍곡선함수 (어려움)
[1, 2].forEach(function (k) {
  add('medium', '쌍곡선함수', 'sech(' + K(k) + ')', C(1, k, 'atan(sinh(' + K(k) + '))'), {
    domain: D.hyp,
    hints: ['$\\operatorname{sech}u=\\dfrac{\\cosh u}{\\cosh^{2}u}=\\dfrac{\\cosh u}{1+\\sinh^{2}u}$',
            '$t=\\sinh ' + K(k) + '$ 로 치환하면 $\\arctan$ 이 나온다.'],
    steps: ['$\\operatorname{sech}' + K(k) + ' = \\dfrac{\\cosh ' + K(k) + '}{1+\\sinh^{2}' + K(k) + '}$',
            '$t=\\sinh ' + K(k) + '$', '$= ' + M.latexOf(C(1, k, 'atan(sinh(' + K(k) + '))')) + '$']
  });
  add('medium', '쌍곡선 홀수차', 'sinh(' + K(k) + ')^3',
      S(C(1, 3 * k, 'cosh(' + K(k) + ')^3'), C(-1, k, 'cosh(' + K(k) + ')')), {
    domain: D.hyp,
    hints: ['$\\sinh^{3}u=\\sinh u(\\cosh^{2}u-1)$', '삼각함수와 달리 $\\cosh^{2}-\\sinh^{2}=1$ 이다.'],
    steps: ['$\\sinh^{3}' + K(k) + ' = (\\cosh^{2}-1)\\sinh$',
            '$= ' + M.latexOf(S(C(1, 3 * k, 'cosh(' + K(k) + ')^3'), C(-1, k, 'cosh(' + K(k) + ')'))) + '$']
  });
  add('medium', '쌍곡선 홀수차', 'cosh(' + K(k) + ')^3',
      S(C(1, k, 'sinh(' + K(k) + ')'), C(1, 3 * k, 'sinh(' + K(k) + ')^3')), {
    domain: D.hyp,
    hints: ['$\\cosh^{3}u=\\cosh u(1+\\sinh^{2}u)$', '$t=\\sinh ' + K(k) + '$ 로 치환한다.'],
    steps: ['$\\cosh^{3}' + K(k) + ' = (1+\\sinh^{2})\\cosh$',
            '$= ' + M.latexOf(S(C(1, k, 'sinh(' + K(k) + ')'), C(1, 3 * k, 'sinh(' + K(k) + ')^3'))) + '$']
  });
  add('medium', '쌍곡선 홀수차', 'tanh(' + K(k) + ')^3',
      S(C(1, k, 'ln(cosh(' + K(k) + '))'), C(-1, 2 * k, 'tanh(' + K(k) + ')^2')), {
    domain: D.hyp,
    hints: ['$\\tanh^{3}u=\\tanh u(1-\\operatorname{sech}^{2}u)$', '$\\tan^{3}$ 문제와 부호가 반대다.'],
    steps: ['$\\tanh^{3}' + K(k) + ' = \\tanh-\\tanh\\operatorname{sech}^{2}$',
            '$= ' + M.latexOf(S(C(1, k, 'ln(cosh(' + K(k) + '))'), C(-1, 2 * k, 'tanh(' + K(k) + ')^2'))) + '$']
  });
});
add('hard', '쌍곡선함수', 'sech(x)^3', '(sech(x)tanh(x)+atan(sinh(x)))/2', {
  domain: D.hyp,
  hints: ['$\\sec^{3}$ 와 같은 구조로 부분적분한다.', '$\\int\\operatorname{sech}x\\,dx=\\arctan(\\sinh x)$ 가 다시 나온다.'],
  steps: ['$I=\\int\\operatorname{sech}^{3}x\\,dx$', '$2I=\\operatorname{sech}x\\tanh x+\\arctan(\\sinh x)$']
});
add('medium', '반복 부분적분', 'x^2*sinh(x)', 'x^2*cosh(x)-2x*sinh(x)+2cosh(x)', {
  domain: D.hyp,
  hints: ['부분적분을 두 번 한다.', '삼각함수와 달리 부호가 계속 $+$ 로 간다.'],
  steps: ['$u=x^{2},\\;dv=\\sinh x\\,dx$', '$x^{2}\\cosh x-2\\int x\\cosh x\\,dx$']
});
add('medium', '반복 부분적분', 'x^2*cosh(x)', 'x^2*sinh(x)-2x*cosh(x)+2sinh(x)', {
  domain: D.hyp,
  hints: ['$u=x^{2},\\;dv=\\cosh x\\,dx$', '두 번 부분적분한다.'],
  steps: ['$u=x^{2},\\;v=\\sinh x$', '$x^{2}\\sinh x-2\\int x\\sinh x\\,dx$']
});
add('medium', '역쌍곡선함수', 'asinh(x)', 'x*asinh(x)-sqrt(x^2+1)', {
  domain: [0.1, 2.5],
  hints: ['$dv=dx$ 로 두고 부분적분한다.', '$\\dfrac{d}{dx}\\operatorname{arsinh}x=\\dfrac{1}{\\sqrt{x^{2}+1}}$'],
  steps: ['$u=\\operatorname{arsinh}x,\\;dv=dx$', '$x\\operatorname{arsinh}x-\\int\\dfrac{x}{\\sqrt{x^{2}+1}}dx$']
});
add('medium', '역쌍곡선함수', 'atanh(x)', 'x*atanh(x)+ln(1-x^2)/2', {
  domain: [-0.7, 0.7],
  hints: ['$dv=dx$ 로 두고 부분적분한다.', '$\\dfrac{d}{dx}\\operatorname{artanh}x=\\dfrac{1}{1-x^{2}}$'],
  steps: ['$u=\\operatorname{artanh}x,\\;dv=dx$', '$x\\operatorname{artanh}x-\\int\\dfrac{x}{1-x^{2}}dx$']
});
add('medium', '역쌍곡선함수', 'ln(x+sqrt(x^2+1))', 'x*asinh(x)-sqrt(x^2+1)', {
  domain: [0.1, 2.5],
  hints: ['$\\ln(x+\\sqrt{x^{2}+1})=\\operatorname{arsinh}x$ 임을 먼저 알아본다.', '그다음은 부분적분이다.'],
  steps: ['$\\ln(x+\\sqrt{x^{2}+1})=\\operatorname{arsinh}x$',
          '$\\int\\operatorname{arsinh}x\\,dx=x\\operatorname{arsinh}x-\\sqrt{x^{2}+1}$']
});
[[2, 1], [3, 1], [3, 2], [1, 2]].forEach(function (q) {
  var a = q[0], b = q[1], den = a * a - b * b;
  add('medium', '쌍곡선함수', 'e^(' + K(a) + ')sinh(' + K(b) + ')',
      'e^(' + K(a) + ')*(' + K(a, 'sinh(' + K(b) + ')') + ' - ' + K(b, 'cosh(' + K(b) + ')') + ')/' + den, {
    domain: [0.05, 1.3],
    hints: ['$\\sinh$ 를 지수로 풀어써도 되고 순환 부분적분을 써도 된다.',
            '분모는 $' + (a * a) + '-' + (b * b) + '=' + den + '$ 이다.'],
    steps: ['$\\sinh ' + K(b) + ' = \\dfrac{e^{' + K(b) + '}-e^{-' + K(b) + '}}{2}$',
            '항별로 지수적분한 뒤 정리한다',
            '$= ' + M.latexOf('e^(' + K(a) + ')*(' + K(a, 'sinh(' + K(b) + ')') + ' - ' + K(b, 'cosh(' + K(b) + ')') + ')/' + den) + '$']
  });
});

// 삼각 유리식
add('medium', '삼각 유리식', '1/(1+sin(x))', 'tan(x)-sec(x)', {
  domain: [0.2, 1.2],
  hints: ['분모·분자에 $1-\\sin x$ 를 곱한다.', '$\\dfrac{1-\\sin x}{\\cos^{2}x}$ 로 정리된다.'],
  steps: ['$\\dfrac{1}{1+\\sin x}\\cdot\\dfrac{1-\\sin x}{1-\\sin x}=\\dfrac{1-\\sin x}{\\cos^{2}x}$',
          '$= \\sec^{2}x-\\sec x\\tan x$']
});
add('medium', '삼각 유리식', '1/(1-sin(x))', 'tan(x)+sec(x)', {
  domain: [0.2, 1.2],
  hints: ['$1+\\sin x$ 를 곱한다.', '부호만 다르고 요령은 같다.'],
  steps: ['$\\dfrac{1+\\sin x}{\\cos^{2}x}=\\sec^{2}x+\\sec x\\tan x$']
});
add('medium', '삼각 유리식', '1/(1+cos(x))', 'tan(x/2)', {
  domain: [0.2, 2.4],
  hints: ['반각공식 $1+\\cos x=2\\cos^{2}\\dfrac{x}{2}$ 를 쓴다.', '$\\dfrac{1}{2}\\sec^{2}\\dfrac{x}{2}$ 가 된다.'],
  steps: ['$1+\\cos x = 2\\cos^{2}\\dfrac{x}{2}$', '$\\dfrac{1}{2}\\int\\sec^{2}\\dfrac{x}{2}dx=\\tan\\dfrac{x}{2}$']
});
add('medium', '삼각 유리식', '1/(1-cos(x))', '-cot(x/2)', {
  domain: [0.4, 2.6],
  hints: ['$1-\\cos x=2\\sin^{2}\\dfrac{x}{2}$ 를 쓴다.', '$\\csc^{2}$ 적분이 된다.'],
  steps: ['$1-\\cos x = 2\\sin^{2}\\dfrac{x}{2}$', '$\\dfrac{1}{2}\\int\\csc^{2}\\dfrac{x}{2}dx=-\\cot\\dfrac{x}{2}$']
});
add('medium', '삼각 유리식', '1/(sin(x)cos(x))', 'ln(tan(x))', {
  domain: [0.3, 1.2], lnAbs: true,
  hints: ['분모·분자에 $\\dfrac{1}{\\cos^{2}x}$ 를 곱해 본다.', '$\\dfrac{\\sec^{2}x}{\\tan x}$ 형태가 된다.'],
  steps: ['$\\dfrac{1}{\\sin x\\cos x}=\\dfrac{\\sec^{2}x}{\\tan x}$', '$u=\\tan x$', '$\\ln|\\tan x|$']
});

// 곱-합 공식
[[2, 1], [3, 1], [3, 2], [4, 1], [5, 2]].forEach(function (q) {
  var a = q[0], b = q[1], m = a - b, pl = a + b;
  add('medium', '곱-합 공식', 'sin(' + K(a) + ')cos(' + K(b) + ')',
      S(C(-1, 2 * m, 'cos(' + K(m) + ')'), C(-1, 2 * pl, 'cos(' + K(pl) + ')')), {
    domain: D.trigW,
    hints: ['$\\sin A\\cos B=\\dfrac{\\sin(A-B)+\\sin(A+B)}{2}$',
            '각이 $' + K(m) + '$ 와 $' + K(pl) + '$ 로 갈라진다.'],
    steps: ['$\\sin ' + K(a) + '\\cos ' + K(b) + ' = \\dfrac{\\sin ' + K(m) + '+\\sin ' + K(pl) + '}{2}$',
            '$= ' + M.latexOf(S(C(-1, 2 * m, 'cos(' + K(m) + ')'), C(-1, 2 * pl, 'cos(' + K(pl) + ')'))) + '$']
  });
  add('medium', '곱-합 공식', 'sin(' + K(a) + ')sin(' + K(b) + ')',
      S(C(1, 2 * m, 'sin(' + K(m) + ')'), C(-1, 2 * pl, 'sin(' + K(pl) + ')')), {
    domain: D.trigW,
    hints: ['$\\sin A\\sin B=\\dfrac{\\cos(A-B)-\\cos(A+B)}{2}$', '두 항을 따로 적분한다.'],
    steps: ['$\\sin ' + K(a) + '\\sin ' + K(b) + ' = \\dfrac{\\cos ' + K(m) + '-\\cos ' + K(pl) + '}{2}$',
            '$= ' + M.latexOf(S(C(1, 2 * m, 'sin(' + K(m) + ')'), C(-1, 2 * pl, 'sin(' + K(pl) + ')'))) + '$']
  });
  add('medium', '곱-합 공식', 'cos(' + K(a) + ')cos(' + K(b) + ')',
      S(C(1, 2 * m, 'sin(' + K(m) + ')'), C(1, 2 * pl, 'sin(' + K(pl) + ')')), {
    domain: D.trigW,
    hints: ['$\\cos A\\cos B=\\dfrac{\\cos(A-B)+\\cos(A+B)}{2}$', '$\\sin\\sin$ 과 부호만 다르다.'],
    steps: ['$\\cos ' + K(a) + '\\cos ' + K(b) + ' = \\dfrac{\\cos ' + K(m) + '+\\cos ' + K(pl) + '}{2}$',
            '$= ' + M.latexOf(S(C(1, 2 * m, 'sin(' + K(m) + ')'), C(1, 2 * pl, 'sin(' + K(pl) + ')'))) + '$']
  });
});

// ================================================================== 몬스터

// x^4 ± 1 계열
add('monster', '4차 유리식', '(x^2+1)/(x^4+1)', 'atan((x^2-1)/(sqrt(2)x))/sqrt(2)', {
  domain: [0.25, 2.6],
  hints: ['분자·분모를 $x^{2}$ 로 나누면 $\\dfrac{1+1/x^{2}}{x^{2}+1/x^{2}}$ 가 된다.',
          '$u=x-\\dfrac{1}{x}$ 로 두면 $du=\\left(1+\\dfrac{1}{x^{2}}\\right)dx$ 이고 분모는 $u^{2}+2$ 다.'],
  steps: ['$\\dfrac{x^{2}+1}{x^{4}+1}=\\dfrac{1+x^{-2}}{x^{2}+x^{-2}}$',
          '$u=x-\\dfrac{1}{x},\\; x^{2}+x^{-2}=u^{2}+2$',
          '$\\int\\dfrac{du}{u^{2}+2}=\\dfrac{1}{\\sqrt2}\\arctan\\dfrac{u}{\\sqrt2}$']
});
add('monster', '4차 유리식', '(x^2-1)/(x^4+1)',
    'ln((x^2-sqrt(2)x+1)/(x^2+sqrt(2)x+1))/(2sqrt(2))', {
  domain: [0.25, 2.6],
  hints: ['이번엔 $u=x+\\dfrac{1}{x}$ 로 두면 분모가 $u^{2}-2$ 가 된다.', '결과는 $\\arctan$ 이 아니라 로그다.'],
  steps: ['$\\dfrac{x^{2}-1}{x^{4}+1}=\\dfrac{1-x^{-2}}{x^{2}+x^{-2}}$',
          '$u=x+\\dfrac{1}{x},\\; x^{2}+x^{-2}=u^{2}-2$',
          '$\\int\\dfrac{du}{u^{2}-2}=\\dfrac{1}{2\\sqrt2}\\ln\\left|\\dfrac{u-\\sqrt2}{u+\\sqrt2}\\right|$']
});
add('monster', '4차 유리식', '1/(x^4+1)',
    'atan((x^2-1)/(sqrt(2)x))/(2sqrt(2)) - ln((x^2-sqrt(2)x+1)/(x^2+sqrt(2)x+1))/(4sqrt(2))', {
  domain: [0.25, 2.6],
  hints: ['$1=\\dfrac{(x^{2}+1)-(x^{2}-1)}{2}$ 로 쪼개면 앞의 두 문제로 환원된다.',
          '$x^{4}+1=(x^{2}-\\sqrt2 x+1)(x^{2}+\\sqrt2 x+1)$ 인수분해를 써도 된다.'],
  steps: ['$\\dfrac{1}{x^{4}+1}=\\dfrac{1}{2}\\cdot\\dfrac{x^{2}+1}{x^{4}+1}-\\dfrac{1}{2}\\cdot\\dfrac{x^{2}-1}{x^{4}+1}$',
          '각각 $u=x\\mp\\dfrac{1}{x}$ 치환으로 계산한다',
          '$\\arctan$ 항과 로그 항이 함께 나온다']
});
add('monster', '4차 유리식', 'x^2/(x^4+1)',
    'atan((x^2-1)/(sqrt(2)x))/(2sqrt(2)) + ln((x^2-sqrt(2)x+1)/(x^2+sqrt(2)x+1))/(4sqrt(2))', {
  domain: [0.25, 2.6],
  hints: ['$x^{2}=\\dfrac{(x^{2}+1)+(x^{2}-1)}{2}$ 로 쪼갠다.', '$\\dfrac{1}{x^{4}+1}$ 문제와 부호 하나만 다르다.'],
  steps: ['$\\dfrac{x^{2}}{x^{4}+1}=\\dfrac{1}{2}\\left(\\dfrac{x^{2}+1}{x^{4}+1}+\\dfrac{x^{2}-1}{x^{4}+1}\\right)$',
          '두 결과를 더한다']
});
add('monster', '4차 유리식', '1/(x^4-1)', 'ln((x-1)/(x+1))/4 - atan(x)/2', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['$x^{4}-1=(x^{2}-1)(x^{2}+1)$ 로 인수분해한다.',
          '$\\dfrac{1}{x^{4}-1}=\\dfrac{1}{2}\\left(\\dfrac{1}{x^{2}-1}-\\dfrac{1}{x^{2}+1}\\right)$'],
  steps: ['$\\dfrac{1}{x^{4}-1}=\\dfrac{1}{2}\\left(\\dfrac{1}{x^{2}-1}-\\dfrac{1}{x^{2}+1}\\right)$',
          '$\\int\\dfrac{dx}{x^{2}-1}=\\dfrac{1}{2}\\ln\\left|\\dfrac{x-1}{x+1}\\right|$']
});
add('hard', '치환적분', 'x/(x^4+2x^2+2)', 'atan(x^2+1)/2', {
  domain: [0.1, 2.5],
  hints: ['분모를 $(x^{2}+1)^{2}+1$ 로 완전제곱한다.', '$u=x^{2}+1$ 로 두면 $\\arctan$ 이 된다.'],
  steps: ['$x^{4}+2x^{2}+2=(x^{2}+1)^{2}+1$', '$u=x^{2}+1,\\;du=2x\\,dx$',
          '$\\dfrac{1}{2}\\int\\dfrac{du}{u^{2}+1}=\\dfrac{\\arctan(x^{2}+1)}{2}$']
});
[2, 3, 4].forEach(function (n) {
  add('hard', '유리식 치환', '1/(x*(x^' + n + '+1))', '(ln(x^' + n + ')-ln(x^' + n + '+1))/' + n, {
    domain: [0.35, 2.6], lnAbs: true,
    hints: ['분자·분모에 $x^{' + (n - 1) + '}$ 을 곱해 $u=x^{' + n + '}$ 를 만든다.',
            '$\\dfrac{1}{u(u+1)}=\\dfrac{1}{u}-\\dfrac{1}{u+1}$'],
    steps: ['$\\dfrac{x^{' + (n - 1) + '}}{x^{' + n + '}(x^{' + n + '}+1)}$', '$u=x^{' + n + '}$',
            '$\\dfrac{1}{' + n + '}\\ln\\left|\\dfrac{x^{' + n + '}}{x^{' + n + '}+1}\\right|$']
  });
});

// 고차 삼각함수
add('monster', '삼각함수 고차', 'sec(x)^5',
    'sec(x)^3*tan(x)/4 + 3*sec(x)tan(x)/8 + 3*ln(sec(x)+tan(x))/8', {
  domain: D.trig, lnAbs: true,
  hints: ['점화식 $\\int\\sec^{n}=\\dfrac{\\sec^{n-2}\\tan}{n-1}+\\dfrac{n-2}{n-1}\\int\\sec^{n-2}$ 를 쓴다.',
          '$\\int\\sec^{3}$ 를 거쳐 $\\int\\sec$ 까지 내려간다.'],
  steps: ['$\\int\\sec^{5}=\\dfrac{\\sec^{3}\\tan}{4}+\\dfrac{3}{4}\\int\\sec^{3}$',
          '$\\int\\sec^{3}=\\dfrac{\\sec\\tan+\\ln|\\sec+\\tan|}{2}$',
          '두 결과를 합친다']
});
add('hard', '삼각함수 고차', 'tan(x)^5', 'tan(x)^4/4 - tan(x)^2/2 - ln(cos(x))', {
  domain: D.trig, lnAbs: true,
  hints: ['$\\tan^{5}=\\tan^{3}(\\sec^{2}-1)$ 로 두 단계 내린다.', '마지막에 $\\int\\tan x\\,dx$ 가 남는다.'],
  steps: ['$\\int\\tan^{5}=\\dfrac{\\tan^{4}}{4}-\\int\\tan^{3}$',
          '$\\int\\tan^{3}=\\dfrac{\\tan^{2}}{2}+\\ln|\\cos x|$']
});
add('medium', '삼각함수 짝수차', 'sin(x)^4', '3x/8 - sin(2x)/4 + sin(4x)/32', {
  domain: D.trigW,
  hints: ['반각공식을 두 번 적용한다.', '$\\sin^{4}=\\left(\\dfrac{1-\\cos 2x}{2}\\right)^{2}$ 에서 $\\cos^{2}2x$ 를 또 내린다.'],
  steps: ['$\\sin^{4}x=\\dfrac{1-2\\cos 2x+\\cos^{2}2x}{4}$',
          '$\\cos^{2}2x=\\dfrac{1+\\cos 4x}{2}$', '$=\\dfrac{3}{8}-\\dfrac{\\cos 2x}{2}+\\dfrac{\\cos 4x}{8}$']
});
add('medium', '삼각함수 짝수차', 'cos(x)^4', '3x/8 + sin(2x)/4 + sin(4x)/32', {
  domain: D.trigW,
  hints: ['$\\cos^{4}=\\left(\\dfrac{1+\\cos 2x}{2}\\right)^{2}$ 로 시작한다.', '$\\sin^{4}$ 와 가운데 항의 부호만 다르다.'],
  steps: ['$\\cos^{4}x=\\dfrac{1+2\\cos 2x+\\cos^{2}2x}{4}$', '$=\\dfrac{3}{8}+\\dfrac{\\cos 2x}{2}+\\dfrac{\\cos 4x}{8}$']
});
add('medium', '삼각함수 홀수차', 'sin(x)^5', '-cos(x)+2cos(x)^3/3-cos(x)^5/5', {
  domain: D.trigW,
  hints: ['$\\sin^{5}=\\sin x(1-\\cos^{2}x)^{2}$ 로 쓴다.', '$u=\\cos x$ 치환 후 전개한다.'],
  steps: ['$\\sin^{5}x=(1-\\cos^{2}x)^{2}\\sin x$', '$u=\\cos x:\\;-\\int(1-u^{2})^{2}du$']
});
add('medium', '삼각함수 홀수차', 'cos(x)^5', 'sin(x)-2sin(x)^3/3+sin(x)^5/5', {
  domain: D.trigW,
  hints: ['$\\cos^{5}=\\cos x(1-\\sin^{2}x)^{2}$ 로 쓴다.', '$u=\\sin x$ 로 치환한다.'],
  steps: ['$\\cos^{5}x=(1-\\sin^{2}x)^{2}\\cos x$', '$u=\\sin x:\\;\\int(1-u^{2})^{2}du$']
});
add('monster', '삼각 유리식', '1/(sin(x)^4+cos(x)^4)', 'atan((tan(x)-cot(x))/sqrt(2))/sqrt(2)', {
  domain: [0.25, 1.3],
  hints: ['분자·분모를 $\\cos^{4}x$ 로 나눠 $\\tan$ 만 남긴다.',
          '$t=\\tan x-\\cot x$ 로 두면 분모가 $t^{2}+2$ 가 된다.'],
  steps: ['$\\sin^{4}+\\cos^{4}=1-\\dfrac{\\sin^{2}2x}{2}$',
          '$\\tan$ 로 정리한 뒤 $t=\\tan x-\\cot x$ 치환', '$\\int\\dfrac{dt}{t^{2}+2}$']
});
add('monster', '삼각 유리식', 'sqrt(tan(x))',
    '(atan((tan(x)-1)/sqrt(2tan(x))) + ln((tan(x)-sqrt(2tan(x))+1)/(tan(x)+sqrt(2tan(x))+1))/2)/sqrt(2)', {
  domain: [0.25, 1.2],
  hints: ['$t=\\sqrt{\\tan x}$ 로 두면 $dx=\\dfrac{2t\\,dt}{1+t^{4}}$ 가 된다.',
          '결국 $\\int\\dfrac{2t^{2}}{1+t^{4}}dt$ 로, $x^{4}+1$ 유리식 문제가 된다.'],
  steps: ['$t=\\sqrt{\\tan x},\\;x=\\arctan t^{2}$', '$\\int\\dfrac{2t^{2}}{1+t^{4}}dt$',
          '$u=t\\mp\\dfrac{1}{t}$ 치환으로 $\\arctan$ 항과 로그 항이 나온다']
});
add('monster', '삼각 유리식', 'sin(x)/(sin(x)+cos(x))', 'x/2 - ln(sin(x)+cos(x))/2', {
  domain: [0.2, 1.2], lnAbs: true,
  hints: ['$\\sin x=\\dfrac{(\\sin+\\cos)-(\\cos-\\sin)}{2}$ 로 쪼갠다.',
          '$\\cos x-\\sin x$ 는 분모의 도함수다.'],
  steps: ['$\\dfrac{\\sin}{\\sin+\\cos}=\\dfrac{1}{2}-\\dfrac{1}{2}\\cdot\\dfrac{\\cos-\\sin}{\\sin+\\cos}$',
          '$\\int\\dfrac{\\cos-\\sin}{\\sin+\\cos}dx=\\ln|\\sin x+\\cos x|$']
});
[[2, 1, 3], [3, 2, 5], [5, 3, 16], [5, 4, 9]].forEach(function (q) {
  var a = q[0], b = q[1], d = q[2];             // d = a^2-b^2
  add('monster', '바이어슈트라스 치환', '1/(' + a + '+' + K(b, 'cos(x)') + ')',
      '2*atan(' + SQ(a - b, a + b) + '*tan(x/2))/' + SQ(d), {
    domain: [0.2, 2.4],
    hints: ['$t=\\tan\\dfrac{x}{2}$ 로 두면 $\\cos x=\\dfrac{1-t^{2}}{1+t^{2}},\\;dx=\\dfrac{2dt}{1+t^{2}}$ 다.',
            '정리하면 $\\int\\dfrac{2\\,dt}{' + (a + b) + '+' + (a - b) + 't^{2}}$ 가 된다.'],
    steps: ['$t=\\tan\\dfrac{x}{2}$',
            '$\\int\\dfrac{2\\,dt}{(' + a + '+' + b + ')+(' + a + '-' + b + ')t^{2}}$',
            '$= \\dfrac{2}{\\sqrt{' + d + '}}\\arctan\\left(\\sqrt{\\dfrac{' + (a - b) + '}{' + (a + b) + '}}\\,t\\right)$']
  });
});

// 반복 부분적분 (고차)
add('medium', '반복 부분적분', 'x^3*e^x', '(x^3-3x^2+6x-6)*e^x', {
  domain: D.all,
  hints: ['부분적분을 세 번 한다.', '계수가 $3!,\\;3\\cdot 2,\\;\\ldots$ 로 떨어지는 규칙을 본다.'],
  steps: ['$\\int x^{3}e^{x}=x^{3}e^{x}-3\\int x^{2}e^{x}$', '$\\int x^{2}e^{x}=(x^{2}-2x+2)e^{x}$',
          '$=(x^{3}-3x^{2}+6x-6)e^{x}$']
});
add('medium', '반복 부분적분', 'x^4*e^x', '(x^4-4x^3+12x^2-24x+24)*e^x', {
  domain: D.all,
  hints: ['부분적분을 네 번 한다.', '표(tabular) 방식으로 정리하면 실수가 줄어든다.'],
  steps: ['$\\int x^{4}e^{x}=x^{4}e^{x}-4\\int x^{3}e^{x}$', '$\\int x^{3}e^{x}=(x^{3}-3x^{2}+6x-6)e^{x}$',
          '$=(x^{4}-4x^{3}+12x^{2}-24x+24)e^{x}$']
});
add('medium', '반복 부분적분', 'x^3*sin(x)', '-x^3*cos(x)+3x^2*sin(x)+6x*cos(x)-6sin(x)', {
  domain: D.trigW,
  hints: ['부분적분을 세 번 한다.', '$\\cos\\to\\sin\\to\\cos$ 순환과 부호를 함께 관리한다.'],
  steps: ['$u=x^{3},\\;dv=\\sin x\\,dx$', '$-x^{3}\\cos x+3\\int x^{2}\\cos x\\,dx$',
          '$=-x^{3}\\cos x+3x^{2}\\sin x+6x\\cos x-6\\sin x$']
});
add('medium', '반복 부분적분', 'x^3*cos(x)', 'x^3*sin(x)+3x^2*cos(x)-6x*sin(x)-6cos(x)', {
  domain: D.trigW,
  hints: ['$u=x^{3},\\;dv=\\cos x\\,dx$ 로 시작한다.', '$\\sin$ 문제와 부호 배치가 다르다.'],
  steps: ['$x^{3}\\sin x-3\\int x^{2}\\sin x\\,dx$', '$=x^{3}\\sin x+3x^{2}\\cos x-6x\\sin x-6\\cos x$']
});
add('medium', '반복 부분적분', 'ln(x)^3', 'x*(ln(x)^3-3ln(x)^2+6ln(x)-6)', {
  domain: D.pos,
  hints: ['$dv=dx$ 로 두고 세 번 부분적분한다.', '$\\int(\\ln x)^{2}dx$ 결과가 중간에 필요하다.'],
  steps: ['$x(\\ln x)^{3}-3\\int(\\ln x)^{2}dx$', '$\\int(\\ln x)^{2}=x(\\ln x)^{2}-2x\\ln x+2x$']
});
add('medium', '반복 부분적분', 'ln(x)^4', 'x*(ln(x)^4-4ln(x)^3+12ln(x)^2-24ln(x)+24)', {
  domain: D.pos,
  hints: ['$t=\\ln x$ 로 치환하면 $\\int t^{4}e^{t}dt$ 가 된다.', '$x^{4}e^{x}$ 문제와 같은 계수가 나온다.'],
  steps: ['$t=\\ln x,\\;dx=e^{t}dt$', '$\\int t^{4}e^{t}dt=(t^{4}-4t^{3}+12t^{2}-24t+24)e^{t}$']
});
add('medium', '부분적분', 'x*ln(x)^2', 'x^2*(ln(x)^2/2 - ln(x)/2 + 1/4)', {
  domain: D.pos,
  hints: ['$u=(\\ln x)^{2},\\;dv=x\\,dx$ 로 둔다.', '남는 적분이 $\\int x\\ln x\\,dx$ 다.'],
  steps: ['$\\dfrac{x^{2}(\\ln x)^{2}}{2}-\\int x\\ln x\\,dx$', '$\\int x\\ln x\\,dx=\\dfrac{x^{2}\\ln x}{2}-\\dfrac{x^{2}}{4}$']
});
add('medium', '부분적분', 'x^2*ln(x)^2', 'x^3*(ln(x)^2/3 - 2ln(x)/9 + 2/27)', {
  domain: D.pos,
  hints: ['$u=(\\ln x)^{2},\\;dv=x^{2}dx$ 로 둔다.', '두 번 부분적분해야 로그가 사라진다.'],
  steps: ['$\\dfrac{x^{3}(\\ln x)^{2}}{3}-\\dfrac{2}{3}\\int x^{2}\\ln x\\,dx$',
          '$\\int x^{2}\\ln x\\,dx=\\dfrac{x^{3}\\ln x}{3}-\\dfrac{x^{3}}{9}$']
});
[2, 3, 4].forEach(function (n) {
  add('medium', '부분적분', 'ln(x)/x^' + n,
      C(-1, n - 1, 'ln(x)/x^' + (n - 1)) + ' - ' + C(1, (n - 1) * (n - 1), '1/x^' + (n - 1)), {
    domain: [0.4, 3.0],
    hints: ['$u=\\ln x,\\;dv=x^{-' + n + '}dx$ 로 둔다.', '$v=-\\dfrac{1}{' + (n - 1) + 'x^{' + (n - 1) + '}}$'],
    steps: ['$u=\\ln x,\\;v=-\\dfrac{1}{' + (n - 1) + 'x^{' + (n - 1) + '}}$',
            '$-\\dfrac{\\ln x}{' + (n - 1) + 'x^{' + (n - 1) + '}}+\\dfrac{1}{' + (n - 1) + '}\\int x^{-' + n + '}dx$']
  });
});

// 세 함수의 곱
add('monster', '삼중 부분적분', 'x*e^x*sin(x)', 'e^x*(x*(sin(x)-cos(x))+cos(x))/2', {
  domain: [0.05, 1.8],
  hints: ['$u=x,\\;dv=e^{x}\\sin x\\,dx$ 로 두면 $v$ 자체가 순환 부분적분이다.',
          '$\\int e^{x}\\sin x\\,dx=\\dfrac{e^{x}(\\sin x-\\cos x)}{2}$ 를 먼저 구한다.'],
  steps: ['$v=\\dfrac{e^{x}(\\sin x-\\cos x)}{2}$', '$xv-\\int v\\,dx$',
          '$=\\dfrac{e^{x}\\left(x(\\sin x-\\cos x)+\\cos x\\right)}{2}$']
});
add('monster', '삼중 부분적분', 'x*e^x*cos(x)', 'e^x*(x*(sin(x)+cos(x))-sin(x))/2', {
  domain: [0.05, 1.8],
  hints: ['$v=\\int e^{x}\\cos x\\,dx=\\dfrac{e^{x}(\\sin x+\\cos x)}{2}$ 를 먼저 구한다.',
          '그다음 $u=x$ 로 부분적분한다.'],
  steps: ['$v=\\dfrac{e^{x}(\\sin x+\\cos x)}{2}$', '$xv-\\int v\\,dx$']
});
[[1, 1], [2, 1]].forEach(function (q) {
  var a = q[0], b = q[1], bb = 2 * b, den = a * a + bb * bb;
  add('medium', '곱-합 + 순환', 'e^(' + K(a) + ')sin(' + K(b) + ')cos(' + K(b) + ')',
      'e^(' + K(a) + ')*(' + K(a, 'sin(' + K(bb) + ')') + ' - ' + K(bb, 'cos(' + K(bb) + ')') + ')/' + (2 * den), {
    domain: [0.05, 1.5],
    hints: ['먼저 $\\sin ' + K(b) + '\\cos ' + K(b) + ' = \\dfrac{\\sin ' + K(bb) + '}{2}$ 로 합친다.',
            '그다음은 표준 순환 부분적분이다.'],
    steps: ['$\\sin ' + K(b) + '\\cos ' + K(b) + ' = \\dfrac{\\sin ' + K(bb) + '}{2}$',
            '$\\dfrac{1}{2}\\int e^{' + K(a) + '}\\sin ' + K(bb) + '\\,dx$',
            '$= ' + M.latexOf('e^(' + K(a) + ')*(' + K(a, 'sin(' + K(bb) + ')') + ' - ' + K(bb, 'cos(' + K(bb) + ')') + ')/' + (2 * den)) + '$']
  });
});

// 역함수 고급
add('hard', '역삼각 고급', 'asin(x)^2', 'x*asin(x)^2+2*sqrt(1-x^2)*asin(x)-2x', {
  domain: D.unit,
  hints: ['$dv=dx$ 로 부분적분하면 $\\int\\dfrac{x\\arcsin x}{\\sqrt{1-x^{2}}}dx$ 가 남는다.',
          '그 적분을 다시 부분적분한다.'],
  steps: ['$x(\\arcsin x)^{2}-2\\int\\dfrac{x\\arcsin x}{\\sqrt{1-x^{2}}}dx$',
          '$\\int\\dfrac{x\\arcsin x}{\\sqrt{1-x^{2}}}dx=-\\sqrt{1-x^{2}}\\arcsin x+x$']
});
add('hard', '역삼각 고급', 'x^2*atan(x)', 'x^3*atan(x)/3 - x^2/6 + ln(1+x^2)/6', {
  domain: [0.1, 2.5],
  hints: ['$u=\\arctan x,\\;dv=x^{2}dx$ 로 둔다.', '남는 $\\int\\dfrac{x^{3}}{1+x^{2}}dx$ 는 나눗셈으로 정리한다.'],
  steps: ['$\\dfrac{x^{3}\\arctan x}{3}-\\dfrac{1}{3}\\int\\dfrac{x^{3}}{1+x^{2}}dx$',
          '$\\dfrac{x^{3}}{1+x^{2}}=x-\\dfrac{x}{1+x^{2}}$']
});
add('hard', '역삼각 고급', 'atan(sqrt(x))', '(x+1)*atan(sqrt(x))-sqrt(x)', {
  domain: [0.2, 3.0],
  hints: ['$t=\\sqrt{x}$ 로 치환한 뒤 부분적분한다.', '$v=\\dfrac{x+1}{1}$ 처럼 적분상수를 잘 고르면 깔끔해진다.'],
  steps: ['$u=\\arctan\\sqrt{x},\\;v=x+1$',
          '$(x+1)\\arctan\\sqrt{x}-\\int\\dfrac{x+1}{2\\sqrt{x}(1+x)}dx$']
});
add('hard', '유리식 부분적분', '1/(x^2+1)^2', 'x/(2*(x^2+1))+atan(x)/2', {
  domain: [-1.5, 2.2],
  hints: ['$x=\\tan\\theta$ 로 치환하면 $\\int\\cos^{2}\\theta\\,d\\theta$ 가 된다.', '점화식으로 풀어도 된다.'],
  steps: ['$x=\\tan\\theta,\\;dx=\\sec^{2}\\theta\\,d\\theta$', '$\\int\\cos^{2}\\theta\\,d\\theta=\\dfrac{\\theta}{2}+\\dfrac{\\sin 2\\theta}{4}$']
});
add('hard', '유리식 부분적분', 'x^2/(x^2+1)^2', 'atan(x)/2 - x/(2*(x^2+1))', {
  domain: [-1.5, 2.2],
  hints: ['$\\dfrac{x^{2}}{(x^{2}+1)^{2}}=\\dfrac{1}{x^{2}+1}-\\dfrac{1}{(x^{2}+1)^{2}}$', '앞 문제 결과를 재활용한다.'],
  steps: ['$\\dfrac{x^{2}}{(x^{2}+1)^{2}}=\\dfrac{1}{x^{2}+1}-\\dfrac{1}{(x^{2}+1)^{2}}$',
          '$\\arctan x-\\left(\\dfrac{x}{2(x^{2}+1)}+\\dfrac{\\arctan x}{2}\\right)$']
});
[1, 2, 4].forEach(function (a) {
  add('hard', '치환+부분분수', 'x^3/(x^2+' + a + ')^2', 'ln(x^2+' + a + ')/2 + ' + a + '/(2*(x^2+' + a + '))', {
    domain: [0.1, 2.5],
    hints: ['$u=x^{2}+' + a + '$ 로 두면 $x^{2}=u-' + a + '$ 다.',
            '$\\dfrac{1}{2}\\int\\dfrac{u-' + a + '}{u^{2}}du$ 로 정리된다.'],
    steps: ['$u=x^{2}+' + a + ',\\;du=2x\\,dx$', '$\\dfrac{1}{2}\\int\\left(\\dfrac{1}{u}-\\dfrac{' + a + '}{u^{2}}\\right)du$']
  });
});
add('hard', '기교', 'e^x*(x^2+1)/(x+1)^2', 'e^x*(x-1)/(x+1)', {
  domain: [0.1, 2.2],
  hints: ['$\\dfrac{x^{2}+1}{(x+1)^{2}}=f(x)+f\'(x)$ 꼴로 쪼갤 수 있는지 본다.',
          '$\\int e^{x}(f+f\')dx=e^{x}f$ 를 쓴다.'],
  steps: ['$\\dfrac{x^{2}+1}{(x+1)^{2}}=\\dfrac{x-1}{x+1}+\\dfrac{2}{(x+1)^{2}}$',
          '$f=\\dfrac{x-1}{x+1},\\;f\'=\\dfrac{2}{(x+1)^{2}}$', '$\\int e^{x}(f+f\')dx=e^{x}f$']
});
[1, 2].forEach(function (a) {
  var a2 = a * a;
  add('hard', '삼각치환 고급', 'x^2*sqrt(' + a2 + '-x^2)',
      C(a2 * a2, 8, 'asin(' + X(a) + ')') + ' - x*(' + a2 + '-2x^2)*sqrt(' + a2 + '-x^2)/8', {
    domain: [-0.72 * a, 0.72 * a],
    hints: ['$x=' + KL(a, '\\sin\\theta') + '$ 로 치환하면 $\\int\\sin^{2}\\theta\\cos^{2}\\theta\\,d\\theta$ 가 된다.',
            '$\\sin^{2}\\theta\\cos^{2}\\theta=\\dfrac{\\sin^{2}2\\theta}{4}$ 로 차수를 내린다.'],
    steps: ['$x=' + KL(a, '\\sin\\theta') + '$', '$' + (a2 * a2) + '\\int\\dfrac{\\sin^{2}2\\theta}{4}d\\theta$',
            '반각공식을 한 번 더 적용한 뒤 $x$ 로 되돌린다']
  });
});

// 쌍곡선 몬스터
add('medium', '쌍곡선 짝수차', 'sech(x)^4', 'tanh(x)-tanh(x)^3/3', {
  domain: D.hyp,
  hints: ['$\\operatorname{sech}^{4}=(1-\\tanh^{2})\\operatorname{sech}^{2}$', '$u=\\tanh x$ 로 치환한다.'],
  steps: ['$\\operatorname{sech}^{4}x=(1-\\tanh^{2}x)\\operatorname{sech}^{2}x$', '$u=\\tanh x:\\;\\int(1-u^{2})du$']
});
add('medium', '쌍곡선 짝수차', 'tanh(x)^4', 'x-tanh(x)-tanh(x)^3/3', {
  domain: D.hyp,
  hints: ['$\\tanh^{4}=\\tanh^{2}(1-\\operatorname{sech}^{2})$ 로 내린다.', '$\\int\\tanh^{2}=x-\\tanh x$ 를 쓴다.'],
  steps: ['$\\int\\tanh^{4}=\\int\\tanh^{2}-\\int\\tanh^{2}\\operatorname{sech}^{2}$',
          '$=x-\\tanh x-\\dfrac{\\tanh^{3}x}{3}$']
});
add('medium', '역쌍곡선 고급', 'x*asinh(x)', '(2x^2+1)*asinh(x)/4 - x*sqrt(x^2+1)/4', {
  domain: [0.1, 2.2],
  hints: ['$u=\\operatorname{arsinh}x,\\;dv=x\\,dx$ 로 둔다.',
          '$v=\\dfrac{x^{2}}{2}$ 대신 $\\dfrac{x^{2}+1}{2}$ 를 쓰면 남는 적분이 간단해진다.'],
  steps: ['$u=\\operatorname{arsinh}x,\\;v=\\dfrac{2x^{2}+1}{4}$ 로 잡는다',
          '남는 적분 $\\int\\dfrac{x^{2}}{\\sqrt{x^{2}+1}}dx$ 를 정리한다']
});
add('medium', '역쌍곡선 고급', 'acosh(x)', 'x*acosh(x)-sqrt(x^2-1)', {
  domain: [1.3, 3.2],
  hints: ['$dv=dx$ 로 부분적분한다.', '$\\dfrac{d}{dx}\\operatorname{arcosh}x=\\dfrac{1}{\\sqrt{x^{2}-1}}$'],
  steps: ['$u=\\operatorname{arcosh}x,\\;dv=dx$', '$x\\operatorname{arcosh}x-\\int\\dfrac{x}{\\sqrt{x^{2}-1}}dx$']
});
add('hard', '쌍곡선 고급', 'x^2*sqrt(x^2+1)',
    'x*(x^2+1)^(3/2)/4 - x*sqrt(x^2+1)/8 - asinh(x)/8', {
  domain: [-1.3, 2.0],
  hints: ['$x=\\sinh\\theta$ 로 치환하면 $\\int\\sinh^{2}\\theta\\cosh^{2}\\theta\\,d\\theta$ 가 된다.',
          '$\\sinh^{2}\\cosh^{2}=\\dfrac{\\sinh^{2}2\\theta}{4}$ 로 내린다.'],
  steps: ['$x=\\sinh\\theta$', '$\\dfrac{1}{4}\\int\\sinh^{2}2\\theta\\,d\\theta$',
          '$\\sinh^{2}u=\\dfrac{\\cosh 2u-1}{2}$ 를 한 번 더 적용한다']
});
add('hard', '쌍곡선 고급', 'sqrt(x^2+1)^3',
    'x*(x^2+1)^(3/2)/4 + 3*x*sqrt(x^2+1)/8 + 3*asinh(x)/8', {
  domain: [-1.3, 2.0],
  hints: ['$(x^{2}+1)^{3/2}$ 이므로 $x=\\sinh\\theta$ 로 두면 $\\int\\cosh^{4}\\theta\\,d\\theta$ 다.',
          '$\\cosh^{4}$ 는 반각공식을 두 번 쓴다.'],
  steps: ['$x=\\sinh\\theta$', '$\\int\\cosh^{4}\\theta\\,d\\theta$',
          '$\\cosh^{2}u=\\dfrac{\\cosh 2u+1}{2}$ 를 두 번 적용']
});
[[2, 1], [3, 2]].forEach(function (q) {
  var a = q[0], b = q[1], den = a * a - b * b;
  add('medium', '쌍곡선 순환', 'e^(' + K(a) + ')cosh(' + K(b) + ')',
      'e^(' + K(a) + ')*(' + K(a, 'cosh(' + K(b) + ')') + ' - ' + K(b, 'sinh(' + K(b) + ')') + ')/' + den, {
    domain: [0.05, 1.3],
    hints: ['$\\cosh$ 를 지수로 풀어 항별로 적분한다.', '분모는 $' + (a * a) + '-' + (b * b) + '=' + den + '$ 이다.'],
    steps: ['$\\cosh ' + K(b) + ' = \\dfrac{e^{' + K(b) + '}+e^{-' + K(b) + '}}{2}$',
            '$= ' + M.latexOf('e^(' + K(a) + ')*(' + K(a, 'cosh(' + K(b) + ')') + ' - ' + K(b, 'sinh(' + K(b) + ')') + ')/' + den) + '$']
  });
});

// 몬스터 추가분 ------------------------------------------------------------

add('medium', '부분적분', 'x*sec(x)^2', 'x*tan(x)+ln(cos(x))', {
  domain: D.trig, lnAbs: true,
  hints: ['$u=x,\\;dv=\\sec^{2}x\\,dx$ 로 둔다.', '남는 $\\int\\tan x\\,dx$ 를 처리한다.'],
  steps: ['$u=x,\\;v=\\tan x$', '$x\\tan x-\\int\\tan x\\,dx = x\\tan x+\\ln|\\cos x|$']
});

add('medium', '반복 부분적분', 'ln(x)^2/x^2', '-(ln(x)^2+2ln(x)+2)/x', {
  domain: [0.4, 3.0],
  hints: ['$u=(\\ln x)^{2},\\;dv=x^{-2}dx$ 로 두고 두 번 부분적분한다.',
          '$\\int\\dfrac{\\ln x}{x^{2}}dx=-\\dfrac{\\ln x+1}{x}$ 를 중간에 쓴다.'],
  steps: ['$-\\dfrac{(\\ln x)^{2}}{x}+2\\int\\dfrac{\\ln x}{x^{2}}dx$',
          '$\\int\\dfrac{\\ln x}{x^{2}}dx=-\\dfrac{\\ln x+1}{x}$',
          '$= -\\dfrac{(\\ln x)^{2}+2\\ln x+2}{x}$']
});
add('hard', '부분적분', 'atan(x)/x^2', '-atan(x)/x+ln(x)-ln(1+x^2)/2', {
  domain: [0.3, 2.5], lnAbs: true,
  hints: ['$u=\\arctan x,\\;dv=x^{-2}dx$ 로 둔다.',
          '남는 $\\int\\dfrac{dx}{x(1+x^{2})}$ 는 부분분수로 나눈다.'],
  steps: ['$-\\dfrac{\\arctan x}{x}+\\int\\dfrac{dx}{x(1+x^{2})}$',
          '$\\dfrac{1}{x(1+x^{2})}=\\dfrac{1}{x}-\\dfrac{x}{1+x^{2}}$']
});
add('hard', '부분적분', 'ln(x)/(1+x)^2', '-ln(x)/(1+x)+ln(x)-ln(1+x)', {
  domain: [0.3, 3.0], lnAbs: true,
  hints: ['$dv=(1+x)^{-2}dx$ 로 두면 $v=-\\dfrac{1}{1+x}$ 다.',
          '남는 $\\int\\dfrac{dx}{x(1+x)}$ 는 부분분수다.'],
  steps: ['$-\\dfrac{\\ln x}{1+x}+\\int\\dfrac{dx}{x(1+x)}$',
          '$\\dfrac{1}{x(1+x)}=\\dfrac{1}{x}-\\dfrac{1}{1+x}$']
});
add('hard', '기교', 'x*e^x/(1+x)^2', 'e^x/(1+x)', {
  domain: [0.2, 2.5],
  hints: ['$\\dfrac{x}{(1+x)^{2}}=\\dfrac{1}{1+x}-\\dfrac{1}{(1+x)^{2}}$ 로 쪼갠다.',
          '$f=\\dfrac{1}{1+x}$ 라 하면 $f\'=-\\dfrac{1}{(1+x)^{2}}$ 이고 $\\int e^{x}(f+f\')dx=e^{x}f$ 다.'],
  steps: ['$\\dfrac{x}{(1+x)^{2}}=\\dfrac{1}{1+x}-\\dfrac{1}{(1+x)^{2}}$',
          '$f=\\dfrac{1}{1+x},\\; f\'=-\\dfrac{1}{(1+x)^{2}}$', '$\\int e^{x}(f+f\')dx=\\dfrac{e^{x}}{1+x}$']
});
add('monster', '기교', '(1+x)/(x*(1+x*e^x))', 'ln(x*e^x)-ln(1+x*e^x)', {
  domain: [0.3, 2.0], lnAbs: true,
  hints: ['$u=xe^{x}$ 로 두면 $du=(1+x)e^{x}dx$ 다.',
          '분자·분모에 $e^{x}$ 를 곱해 $u$ 를 만들어 낸다.'],
  steps: ['분자·분모에 $e^{x}$ 를 곱한다: $\\dfrac{(1+x)e^{x}}{xe^{x}(1+xe^{x})}$',
          '$u=xe^{x}$', '$\\int\\dfrac{du}{u(1+u)}=\\ln\\left|\\dfrac{u}{1+u}\\right|$']
});

// 삼각 유리식 (몬스터)
add('hard', '삼각 유리식', 'sin(x)/(1+sin(x))', 'x-tan(x)+sec(x)', {
  domain: [0.2, 1.2],
  hints: ['$\\dfrac{\\sin x}{1+\\sin x}=1-\\dfrac{1}{1+\\sin x}$ 로 쪼갠다.',
          '$\\int\\dfrac{dx}{1+\\sin x}=\\tan x-\\sec x$ 를 쓴다.'],
  steps: ['$\\dfrac{\\sin x}{1+\\sin x}=1-\\dfrac{1}{1+\\sin x}$',
          '$\\int\\dfrac{dx}{1+\\sin x}=\\tan x-\\sec x$']
});
add('hard', '삼각 유리식', 'cos(x)/(1+cos(x))', 'x-tan(x/2)', {
  domain: [0.2, 2.4],
  hints: ['$\\dfrac{\\cos x}{1+\\cos x}=1-\\dfrac{1}{1+\\cos x}$', '$\\int\\dfrac{dx}{1+\\cos x}=\\tan\\dfrac{x}{2}$'],
  steps: ['$\\dfrac{\\cos x}{1+\\cos x}=1-\\dfrac{1}{1+\\cos x}$', '$1+\\cos x=2\\cos^{2}\\dfrac{x}{2}$']
});
[[2, 1, 3], [3, 2, 5], [5, 3, 16]].forEach(function (q) {
  var a = q[0], b = q[1], d = q[2];
  add('monster', '바이어슈트라스 치환', '1/(' + a + '+' + K(b, 'sin(x)') + ')',
      '2*atan((' + K(a, 'tan(x/2)') + '+' + b + ')/' + SQ(d) + ')/' + SQ(d), {
    domain: [0.2, 2.4],
    hints: ['$t=\\tan\\dfrac{x}{2}$ 로 두면 $\\sin x=\\dfrac{2t}{1+t^{2}}$ 다.',
            '분모를 정리하면 $' + a + 't^{2}+' + (2 * b) + 't+' + a + '$ 가 되어 완전제곱이 필요하다.'],
    steps: ['$t=\\tan\\dfrac{x}{2},\\;dx=\\dfrac{2dt}{1+t^{2}}$',
            '$\\int\\dfrac{2\\,dt}{' + a + 't^{2}+' + (2 * b) + 't+' + a + '}$',
            '완전제곱 후 $\\arctan$ 형태로 정리한다']
  });
});

// 근호가 있는 유리식
add('hard', '삼각치환 고급', 'sqrt(x^2+1)/x', 'sqrt(x^2+1)-ln((1+sqrt(x^2+1))/x)', {
  domain: [0.35, 2.6], lnAbs: true,
  hints: ['$x=\\sinh\\theta$ 로 두면 $\\int\\dfrac{\\cosh^{2}\\theta}{\\sinh\\theta}d\\theta$ 가 된다.',
          '$u=\\sqrt{x^{2}+1}$ 치환으로 유리식으로 바꿔도 된다.'],
  steps: ['$u=\\sqrt{x^{2}+1},\\;u\\,du=x\\,dx$', '$\\int\\dfrac{u^{2}}{u^{2}-1}du$',
          '$= u+\\dfrac{1}{2}\\ln\\left|\\dfrac{u-1}{u+1}\\right|$ 를 정리한다']
});
add('hard', '삼각치환 고급', 'sqrt(x^2-1)/x', 'sqrt(x^2-1)-atan(sqrt(x^2-1))', {
  domain: [1.3, 3.2],
  hints: ['$x=\\sec\\theta$ 로 두면 $\\int\\tan^{2}\\theta\\,d\\theta$ 가 된다.',
          '$\\tan^{2}=\\sec^{2}-1$ 로 내린다.'],
  steps: ['$x=\\sec\\theta$', '$\\int\\tan^{2}\\theta\\,d\\theta=\\tan\\theta-\\theta$',
          '$\\tan\\theta=\\sqrt{x^{2}-1},\\;\\theta=\\operatorname{arcsec}x$']
});

// x^n 치환 + 부분적분
add('hard', '치환+부분적분', 'x^3*e^(x^2)', 'e^(x^2)*(x^2-1)/2', {
  domain: [0.1, 1.3],
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac{1}{2}\\int ue^{u}du$ 가 된다.', '그다음은 부분적분이다.'],
  steps: ['$u=x^{2},\\;du=2x\\,dx$', '$\\dfrac{1}{2}\\int ue^{u}du=\\dfrac{(u-1)e^{u}}{2}$']
});
add('hard', '치환+부분적분', 'x^5*e^(x^2)', 'e^(x^2)*(x^4-2x^2+2)/2', {
  domain: [0.1, 1.2],
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac{1}{2}\\int u^{2}e^{u}du$ 다.', '부분적분을 두 번 한다.'],
  steps: ['$u=x^{2}$', '$\\dfrac{1}{2}\\int u^{2}e^{u}du=\\dfrac{(u^{2}-2u+2)e^{u}}{2}$']
});
add('hard', '치환+부분적분', 'x^3*sin(x^2)', '(sin(x^2)-x^2*cos(x^2))/2', {
  domain: [0.2, 1.6],
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac{1}{2}\\int u\\sin u\\,du$ 가 된다.', '부분적분으로 마무리한다.'],
  steps: ['$u=x^{2},\\;du=2x\\,dx$', '$\\dfrac{1}{2}\\int u\\sin u\\,du=\\dfrac{\\sin u-u\\cos u}{2}$']
});
add('medium', '부분적분', 'x*csc(x)^2', '-x*cot(x)+ln(sin(x))', {
  domain: [0.45, 2.3], lnAbs: true,
  hints: ['$u=x,\\;dv=\\csc^{2}x\\,dx$ 로 둔다.', '남는 $\\int\\cot x\\,dx$ 를 처리한다.'],
  steps: ['$u=x,\\;v=-\\cot x$', '$-x\\cot x+\\int\\cot x\\,dx=-x\\cot x+\\ln|\\sin x|$']
});

// 쌍곡선 4차
add('medium', '쌍곡선 짝수차', 'sinh(x)^4', '3x/8 - sinh(2x)/4 + sinh(4x)/32', {
  domain: [0.2, 1.4],
  hints: ['$\\sinh^{2}u=\\dfrac{\\cosh 2u-1}{2}$ 를 두 번 적용한다.', '$\\sin^{4}$ 과 형태가 비슷하지만 부호가 다르다.'],
  steps: ['$\\sinh^{4}x=\\dfrac{(\\cosh 2x-1)^{2}}{4}$',
          '$\\cosh^{2}2x=\\dfrac{\\cosh 4x+1}{2}$', '$=\\dfrac{3}{8}-\\dfrac{\\cosh 2x}{2}+\\dfrac{\\cosh 4x}{8}$']
});
add('medium', '쌍곡선 짝수차', 'cosh(x)^4', '3x/8 + sinh(2x)/4 + sinh(4x)/32', {
  domain: [0.2, 1.4],
  hints: ['$\\cosh^{2}u=\\dfrac{\\cosh 2u+1}{2}$ 를 두 번 적용한다.', '$\\sinh^{4}$ 과 가운데 항의 부호만 다르다.'],
  steps: ['$\\cosh^{4}x=\\dfrac{(\\cosh 2x+1)^{2}}{4}$', '$=\\dfrac{3}{8}+\\dfrac{\\cosh 2x}{2}+\\dfrac{\\cosh 4x}{8}$']
});

// ================================================================== 어려움 추가분
// (다른 데일리 적분 사이트 / 적분 대회(Integration Bee) 단골 문제들을 참고해 보강)

add('medium', '부분적분', 'x*arctan(x)', '(x^2+1)*arctan(x)/2 - x/2', {
  domain: [0.3, 2.4],
  hints: ['$u=\\arctan x,\;dv=x\\,dx$ 로 잡되 $v=\\dfrac{x^{2}+1}{2}$ 로 두면 편하다.',
          '남는 적분이 $\\dfrac12\\int dx$ 로 깔끔해진다.'],
  steps: ['$v=\\dfrac{x^{2}+1}{2}$ 로 두면 $\\int x\\arctan x\\,dx=\\dfrac{(x^{2}+1)\\arctan x}{2}-\\dfrac12\\int dx$',
          '$=\\dfrac{(x^{2}+1)\\arctan x}{2}-\\dfrac{x}{2}$']
});
add('medium', '부분적분', 'x^2*e^x', 'e^x*(x^2-2*x+2)', {
  domain: [0.2, 2.2],
  hints: ['부분적분을 두 번 한다.', '$\\int P(x)e^{x}dx=e^{x}\\left(P-P\'+P\'\'-\\cdots\\right)$ 를 쓰면 한 줄이다.'],
  steps: ['$\\int x^{2}e^{x}=x^{2}e^{x}-2\\int xe^{x}$', '$\\int xe^{x}=(x-1)e^{x}$',
          '$=e^{x}(x^{2}-2x+2)$']
});
add('medium', '순환 부분적분', 'e^x*sin(x)', 'e^x*(sin(x)-cos(x))/2', {
  domain: [0.2, 2.4],
  hints: ['부분적분을 두 번 하면 원래 적분 $I$ 가 다시 나온다.', '$I=-e^{x}\\cos x+e^{x}\\sin x-I$ 를 $I$ 에 대해 푼다.'],
  steps: ['$I=\\int e^{x}\\sin x\\,dx$', '두 번 부분적분하면 $I=e^{x}(\\sin x-\\cos x)-I$',
          '$I=\\dfrac{e^{x}(\\sin x-\\cos x)}{2}$']
});
add('medium', '부분적분', 'ln(x)^2', 'x*ln(x)^2-2*x*ln(x)+2*x', {
  domain: D.pos,
  hints: ['$u=\\ln^{2}x,\;dv=dx$ 로 부분적분한다.', '남는 $\\int\\ln x\\,dx=x\\ln x-x$ 를 쓴다.'],
  steps: ['$\\int\\ln^{2}x\\,dx=x\\ln^{2}x-2\\int\\ln x\\,dx$', '$=x\\ln^{2}x-2x\\ln x+2x$']
});
add('medium', '부분적분', 'ln(x)^3', 'x*ln(x)^3-3*x*ln(x)^2+6*x*ln(x)-6*x', {
  domain: D.pos,
  hints: ['$\\int\\ln^{n}x\\,dx=x\\ln^{n}x-n\\int\\ln^{n-1}x\\,dx$ 점화식을 쓴다.', '$\\ln^{2}$ 결과를 그대로 대입한다.'],
  steps: ['$\\int\\ln^{3}x=x\\ln^{3}x-3\\int\\ln^{2}x$',
          '$\\int\\ln^{2}x=x\\ln^{2}x-2x\\ln x+2x$', '정리하면 $x(\\ln^{3}x-3\\ln^{2}x+6\\ln x-6)$']
});
add('medium', '지수 유리식', '1/(1+e^x)', 'x-ln(1+e^x)', {
  domain: [-1.5, 1.7],
  hints: ['$\\dfrac{1}{1+e^{x}}=1-\\dfrac{e^{x}}{1+e^{x}}$ 로 쪼갠다.', '뒤 항은 $\\ln(1+e^{x})$ 의 미분 꼴이다.'],
  steps: ['$\\dfrac{1}{1+e^{x}}=1-\\dfrac{e^{x}}{1+e^{x}}$', '$=x-\\ln(1+e^{x})$']
});
add('medium', '지수 치환', 'e^x/(1+e^(2x))', 'arctan(e^x)', {
  domain: [-1.2, 1.6],
  hints: ['$u=e^{x}$ 로 두면 $du=e^{x}dx$ 다.', '$\\int\\dfrac{du}{1+u^{2}}=\\arctan u$'],
  steps: ['$u=e^{x}$', '$\\int\\dfrac{du}{1+u^{2}}=\\arctan(e^{x})$']
});
add('medium', '지수 유리식', '1/(e^x+e^(-x))', 'arctan(e^x)', {
  domain: [-1.2, 1.6],
  hints: ['분자·분모에 $e^{x}$ 를 곱한다.', '$u=e^{x}$ 치환이면 $\\arctan$ 이다.'],
  steps: ['$\\dfrac{1}{e^{x}+e^{-x}}=\\dfrac{e^{x}}{e^{2x}+1}$', '$u=e^{x}:\;\\arctan(e^{x})$']
});
add('hard', '지수 치환', 'e^(2*x)/sqrt(e^x+1)', '2*(e^x+1)^(3/2)/3-2*sqrt(e^x+1)', {
  domain: [-1, 1.6],
  hints: ['$u=e^{x}$ 로 두면 $\\int\\dfrac{u}{\\sqrt{u+1}}du$ 가 된다.', '$u=(u+1)-1$ 로 쪼갠다.'],
  steps: ['$u=e^{x}$', '$\\int\\dfrac{(u+1)-1}{\\sqrt{u+1}}du=\\dfrac{2(u+1)^{3/2}}{3}-2\\sqrt{u+1}$']
});
add('medium', '삼각 치환', '1/(x^2*sqrt(x^2-1))', 'sqrt(x^2-1)/x', {
  domain: D.gt1,
  hints: ['$x=\\sec\\theta$ 로 두면 $\\int\\cos\\theta\\,d\\theta$ 만 남는다.', '결과를 다시 $x$ 로 되돌리면 $\\sin\\theta=\\dfrac{\\sqrt{x^{2}-1}}{x}$'],
  steps: ['$x=\\sec\\theta,\;dx=\\sec\\theta\\tan\\theta\\,d\\theta$',
          '$\\int\\cos\\theta\\,d\\theta=\\sin\\theta=\\dfrac{\\sqrt{x^{2}-1}}{x}$']
});
add('medium', '삼각 치환', '1/(x*sqrt(x^2-1))', 'arctan(sqrt(x^2-1))', {
  domain: D.gt1,
  hints: ['$u=\\sqrt{x^{2}-1}$ 로 두면 $x\\,dx=u\\,du$ 다.', '분모가 $u^{2}+1$ 로 바뀐다.'],
  steps: ['$u=\\sqrt{x^{2}-1},\;x^{2}=u^{2}+1$', '$\\int\\dfrac{du}{u^{2}+1}=\\arctan\\sqrt{x^{2}-1}$']
});
add('hard', '삼각 치환', 'sqrt(x^2-1)/x', 'sqrt(x^2-1)-arctan(sqrt(x^2-1))', {
  domain: D.gt1,
  hints: ['$u=\\sqrt{x^{2}-1}$ 치환 후 $\\dfrac{u^{2}}{u^{2}+1}=1-\\dfrac{1}{u^{2}+1}$ 로 쪼갠다.', '$\\arctan$ 항이 남는다.'],
  steps: ['$u=\\sqrt{x^{2}-1}$', '$\\int\\dfrac{u^{2}}{u^{2}+1}du=u-\\arctan u$']
});
add('hard', '쌍곡선 치환', 'sqrt(1+x^2)/x^2', 'asinh(x)-sqrt(1+x^2)/x', {
  domain: D.pos,
  hints: ['$u=\\sqrt{1+x^{2}},\;dv=\\dfrac{dx}{x^{2}}$ 로 부분적분한다.', '남는 적분이 $\\int\\dfrac{dx}{\\sqrt{1+x^{2}}}$ 다.'],
  steps: ['$\\int\\dfrac{\\sqrt{1+x^{2}}}{x^{2}}dx=-\\dfrac{\\sqrt{1+x^{2}}}{x}+\\int\\dfrac{dx}{\\sqrt{1+x^{2}}}$',
          '$=\\operatorname{arsinh}x-\\dfrac{\\sqrt{1+x^{2}}}{x}$']
});
add('hard', '로그 적분', 'sqrt(x^2+1)/x', 'sqrt(x^2+1)-ln((1+sqrt(x^2+1))/x)', {
  domain: D.pos,
  hints: ['$u=\\sqrt{x^{2}+1}$ 로 두면 $\\int\\dfrac{u^{2}}{u^{2}-1}du$ 다.', '$\\dfrac{u^{2}}{u^{2}-1}=1+\\dfrac{1}{u^{2}-1}$'],
  steps: ['$u=\\sqrt{x^{2}+1},\;x\\,dx=u\\,du$',
          '$\\int\\left(1+\\dfrac{1}{u^{2}-1}\\right)du=u+\\dfrac12\\ln\\dfrac{u-1}{u+1}$',
          '$=\\sqrt{x^{2}+1}-\\ln\\dfrac{1+\\sqrt{x^{2}+1}}{x}$']
});
add('medium', '로그 미분', 'ln(x)/x^2', '-(ln(x)+1)/x', {
  domain: D.pos,
  hints: ['$u=\\ln x,\;dv=x^{-2}dx$ 로 부분적분한다.', '$v=-\\dfrac1x$'],
  steps: ['$=-\\dfrac{\\ln x}{x}+\\int\\dfrac{dx}{x^{2}}$', '$=-\\dfrac{\\ln x+1}{x}$']
});
add('hard', '역삼각 부분적분', 'arctan(sqrt(x))', '(x+1)*arctan(sqrt(x))-sqrt(x)', {
  domain: D.pos,
  hints: ['부분적분 후 $\\int\\dfrac{\\sqrt{x}}{2(1+x)}dx$ 가 남는다.', '$v=x+1$ 로 잡으면 남는 적분이 $\\dfrac12\\int x^{-1/2}dx$ 로 줄어든다.'],
  steps: ['$v=x+1$ 로 부분적분: $(x+1)\\arctan\\sqrt{x}-\\int\\dfrac{x+1}{2\\sqrt{x}(1+x)}dx$',
          '$=(x+1)\\arctan\\sqrt{x}-\\sqrt{x}$']
});
add('hard', '순환 부분적분', 'sin(ln(x))', 'x*(sin(ln(x))-cos(ln(x)))/2', {
  domain: D.pos,
  hints: ['$t=\\ln x$ 로 두면 $\\int e^{t}\\sin t\\,dt$ 가 된다.', '$e^{x}\\sin x$ 문제와 같은 꼴이다.'],
  steps: ['$t=\\ln x,\;dx=e^{t}dt$', '$\\int e^{t}\\sin t\\,dt=\\dfrac{e^{t}(\\sin t-\\cos t)}{2}$',
          '$=\\dfrac{x(\\sin\\ln x-\\cos\\ln x)}{2}$']
});
add('hard', '부분적분', 'ln(x+sqrt(x^2+1))', 'x*asinh(x)-sqrt(x^2+1)', {
  domain: [0.2, 2.4],
  hints: ['피적분함수는 $\\operatorname{arsinh}x$ 다.', '$dv=dx$ 로 부분적분하면 $\\int\\dfrac{x}{\\sqrt{x^{2}+1}}dx$ 가 남는다.'],
  steps: ['$\\int\\operatorname{arsinh}x\\,dx=x\\operatorname{arsinh}x-\\int\\dfrac{x\\,dx}{\\sqrt{x^{2}+1}}$',
          '$=x\\operatorname{arsinh}x-\\sqrt{x^{2}+1}$']
});
add('medium', '부분적분', 'x*sec(x)^2', 'x*tan(x)+ln(cos(x))', {
  domain: D.trig, lnAbs: true,
  hints: ['$dv=\\sec^{2}x\\,dx\\Rightarrow v=\\tan x$', '남는 $\\int\\tan x\\,dx=-\\ln|\\cos x|$ 를 쓴다.'],
  steps: ['$\\int x\\sec^{2}x\\,dx=x\\tan x-\\int\\tan x\\,dx$', '$=x\\tan x+\\ln|\\cos x|$']
});
add('hard', '미분 꼴 알아보기', 'x*e^x/(1+x)^2', 'e^x/(1+x)', {
  domain: [0.2, 2.4],
  hints: ['$\\dfrac{x}{(1+x)^{2}}=\\dfrac{1}{1+x}-\\dfrac{1}{(1+x)^{2}}$ 로 쪼갠다.',
          '$\\left(\\dfrac{e^{x}}{1+x}\\right)\'=e^{x}\\left(\\dfrac{1}{1+x}-\\dfrac{1}{(1+x)^{2}}\\right)$'],
  steps: ['$\\dfrac{xe^{x}}{(1+x)^{2}}=e^{x}\\left(\\dfrac{1}{1+x}-\\dfrac{1}{(1+x)^{2}}\\right)$',
          '$\\int e^{x}(f+f\')dx=e^{x}f$ 꼴이므로 $f=\\dfrac{1}{1+x}$', '$=\\dfrac{e^{x}}{1+x}$']
});
add('hard', '미분 꼴 알아보기', 'e^x*(x^2+1)/(x+1)^2', 'e^x*(x-1)/(x+1)', {
  domain: [0.2, 2.4],
  hints: ['$\\int e^{x}(f+f\')dx=e^{x}f$ 를 노린다.', '$f=\\dfrac{x-1}{x+1}$ 로 두고 $f\'=\\dfrac{2}{(x+1)^{2}}$ 를 확인한다.'],
  steps: ['$\\dfrac{x^{2}+1}{(x+1)^{2}}=\\dfrac{x-1}{x+1}+\\dfrac{2}{(x+1)^{2}}$',
          '$f=\\dfrac{x-1}{x+1},\;f\'=\\dfrac{2}{(x+1)^{2}}$', '$=\\dfrac{e^{x}(x-1)}{x+1}$']
});
add('hard', '미분 꼴 알아보기', 'e^x*(1/x-1/x^2)', 'e^x/x', {
  domain: D.pos,
  hints: ['$f=\\dfrac1x$ 라 하면 $f\'=-\\dfrac{1}{x^{2}}$ 다.', '$\\int e^{x}(f+f\')dx=e^{x}f$'],
  steps: ['$f=\\dfrac1x$', '$\\int e^{x}(f+f\')dx=e^{x}f=\\dfrac{e^{x}}{x}$']
});
add('hard', '미분 꼴 알아보기', 'e^x*(x*ln(x)+1)/x', 'e^x*ln(x)', {
  domain: D.pos,
  hints: ['$\\dfrac{x\\ln x+1}{x}=\\ln x+\\dfrac1x$ 로 정리한다.', '$f=\\ln x,\;f\'=\\dfrac1x$'],
  steps: ['$e^{x}\\left(\\ln x+\\dfrac1x\\right)$', '$\\int e^{x}(f+f\')dx=e^{x}\\ln x$']
});
add('hard', '미분 꼴 알아보기', '(ln(x)-1)/ln(x)^2', 'x/ln(x)', {
  domain: [1.4, 4.2],
  hints: ['$\\left(\\dfrac{x}{\\ln x}\\right)\'$ 를 직접 계산해 본다.', '$\\dfrac{\\ln x-1}{\\ln^{2}x}$ 가 바로 그 도함수다.'],
  steps: ['$\\left(\\dfrac{x}{\\ln x}\\right)\'=\\dfrac{\\ln x-x\\cdot\\frac1x}{\\ln^{2}x}=\\dfrac{\\ln x-1}{\\ln^{2}x}$',
          '따라서 원시함수는 $\\dfrac{x}{\\ln x}$']
});
add('hard', '미분 꼴 알아보기', '(x*cos(x)-sin(x))/x^2', 'sin(x)/x', {
  domain: [0.3, 2.8],
  hints: ['몫의 미분법을 거꾸로 읽는다.', '$\\left(\\dfrac{\\sin x}{x}\\right)\'=\\dfrac{x\\cos x-\\sin x}{x^{2}}$'],
  steps: ['$\\left(\\dfrac{\\sin x}{x}\\right)\'=\\dfrac{x\\cos x-\\sin x}{x^{2}}$', '$=\\dfrac{\\sin x}{x}$']
});
add('hard', '로그 치환', 'e^x*(x+1)/(x*e^x+1)', 'ln(x*e^x+1)', {
  domain: [0.2, 2.2],
  hints: ['$u=xe^{x}$ 로 두면 $du=(x+1)e^{x}dx$ 다.', '$\\int\\dfrac{du}{u+1}$ 만 남는다.'],
  steps: ['$u=xe^{x},\;du=(1+x)e^{x}dx$', '$\\int\\dfrac{du}{1+u}=\\ln|1+xe^{x}|$']
});
add('medium', '유리 치환', '1/(sqrt(x)*(1+x))', '2*arctan(sqrt(x))', {
  domain: D.pos,
  hints: ['$u=\\sqrt{x}$ 로 두면 $dx=2u\\,du$ 다.', '$\\int\\dfrac{2\\,du}{1+u^{2}}$'],
  steps: ['$u=\\sqrt x$', '$\\int\\dfrac{2du}{1+u^{2}}=2\\arctan\\sqrt{x}$']
});
add('hard', '유리화', 'sqrt((1-x)/(1+x))', 'arcsin(x)+sqrt(1-x^2)', {
  domain: D.unit,
  hints: ['분자·분모에 $\\sqrt{1-x}$ 를 곱해 $\\dfrac{1-x}{\\sqrt{1-x^{2}}}$ 로 만든다.',
          '$\\dfrac{1}{\\sqrt{1-x^{2}}}$ 와 $\\dfrac{-x}{\\sqrt{1-x^{2}}}$ 로 쪼갠다.'],
  steps: ['$\\sqrt{\\dfrac{1-x}{1+x}}=\\dfrac{1-x}{\\sqrt{1-x^{2}}}$',
          '$=\\arcsin x+\\sqrt{1-x^{2}}$']
});
add('hard', '유리화', 'x/(sqrt(1+x)+sqrt(1-x))', '((1+x)^(3/2)+(1-x)^(3/2))/3', {
  domain: D.unit,
  hints: ['분모를 유리화하면 분모가 $2x$ 가 되어 $x$ 가 약분된다.',
          '$\\dfrac{\\sqrt{1+x}-\\sqrt{1-x}}{2}$ 만 적분하면 된다.'],
  steps: ['$\\dfrac{x}{\\sqrt{1+x}+\\sqrt{1-x}}=\\dfrac{x(\\sqrt{1+x}-\\sqrt{1-x})}{2x}$',
          '$=\\dfrac12\\int(\\sqrt{1+x}-\\sqrt{1-x})dx=\\dfrac{(1+x)^{3/2}+(1-x)^{3/2}}{3}$']
});
add('hard', '부분분수', 'x^2/(x^2+1)^2', 'arctan(x)/2-x/(2*(x^2+1))', {
  domain: [-1.5, 1.7],
  hints: ['$\\dfrac{x^{2}}{(x^{2}+1)^{2}}=\\dfrac{1}{x^{2}+1}-\\dfrac{1}{(x^{2}+1)^{2}}$',
          '$\\int\\dfrac{dx}{(x^{2}+1)^{2}}=\\dfrac{x}{2(x^{2}+1)}+\\dfrac{\\arctan x}{2}$'],
  steps: ['$\\dfrac{x^{2}}{(x^{2}+1)^{2}}=\\dfrac{1}{x^{2}+1}-\\dfrac{1}{(x^{2}+1)^{2}}$',
          '$=\\dfrac{\\arctan x}{2}-\\dfrac{x}{2(x^{2}+1)}$']
});
add('hard', '부분분수', '1/(x^4+x^2)', '-1/x-arctan(x)', {
  domain: D.poly,
  hints: ['$\\dfrac{1}{x^{2}(x^{2}+1)}=\\dfrac{1}{x^{2}}-\\dfrac{1}{x^{2}+1}$', '두 항 모두 기본 적분이다.'],
  steps: ['$\\dfrac{1}{x^{2}(x^{2}+1)}=\\dfrac{1}{x^{2}}-\\dfrac{1}{x^{2}+1}$', '$=-\\dfrac1x-\\arctan x$']
});
add('hard', '부분분수', 'x/((x-1)*(x-2)*(x-3))', 'ln(x-1)/2-2*ln(x-2)+3*ln(x-3)/2', {
  domain: [3.4, 6.2], lnAbs: true,
  hints: ['헤비사이드 가리기(cover-up)로 세 계수를 한 번에 구한다.',
          '$x=1,2,3$ 을 각각 대입하면 $\\dfrac12,\\,-2,\\,\\dfrac32$ 가 나온다.'],
  steps: ['$\\dfrac{x}{(x-1)(x-2)(x-3)}=\\dfrac{1/2}{x-1}-\\dfrac{2}{x-2}+\\dfrac{3/2}{x-3}$',
          '각 항을 로그로 적분한다']
});
add('hard', '부분분수', '1/(1-x^4)', 'ln((1+x)/(1-x))/4+arctan(x)/2', {
  domain: [-0.8, 0.8],
  hints: ['$1-x^{4}=(1-x^{2})(1+x^{2})$ 로 인수분해한다.',
          '$\\dfrac{1}{1-x^{4}}=\\dfrac12\\left(\\dfrac{1}{1-x^{2}}+\\dfrac{1}{1+x^{2}}\\right)$'],
  steps: ['$\\dfrac{1}{1-x^{4}}=\\dfrac12\\left(\\dfrac{1}{1-x^{2}}+\\dfrac{1}{1+x^{2}}\\right)$',
          '$\\int\\dfrac{dx}{1-x^{2}}=\\dfrac12\\ln\\left|\\dfrac{1+x}{1-x}\\right|$']
});
add('medium', '치환적분', 'cos(x)/(1+sin(x)^2)', 'arctan(sin(x))', {
  domain: D.trigW,
  hints: ['$u=\\sin x$ 로 둔다.', '$\\int\\dfrac{du}{1+u^{2}}=\\arctan u$'],
  steps: ['$u=\\sin x,\;du=\\cos x\\,dx$', '$\\arctan(\\sin x)$']
});
add('medium', '치환적분', 'x^3/sqrt(x^2+1)', '(x^2+1)^(3/2)/3-sqrt(x^2+1)', {
  domain: D.poly,
  hints: ['$u=x^{2}+1$ 로 두고 $x^{2}=u-1$ 을 쓴다.', '$\\dfrac12\\int\\dfrac{u-1}{\\sqrt u}du$'],
  steps: ['$u=x^{2}+1$', '$\\dfrac12\\int(u^{1/2}-u^{-1/2})du=\\dfrac{u^{3/2}}{3}-u^{1/2}$']
});
add('medium', '치환적분', 'e^(sqrt(x))', '2*e^(sqrt(x))*(sqrt(x)-1)', {
  domain: D.pos,
  hints: ['$u=\\sqrt x$ 로 두면 $dx=2u\\,du$ 다.', '$2\\int ue^{u}du$ 를 부분적분한다.'],
  steps: ['$u=\\sqrt x,\;dx=2u\\,du$', '$2\\int ue^{u}du=2e^{u}(u-1)$',
          '$=2e^{\\sqrt x}(\\sqrt x-1)$']
});
add('medium', '치환적분', 'arctan(x)/(1+x^2)', 'arctan(x)^2/2', {
  domain: D.all,
  hints: ['$u=\\arctan x$ 로 두면 $du=\\dfrac{dx}{1+x^{2}}$ 다.', '$\\int u\\,du$ 만 남는다.'],
  steps: ['$u=\\arctan x$', '$\\int u\\,du=\\dfrac{\\arctan^{2}x}{2}$']
});
add('medium', '치환적분', 'arcsin(x)/sqrt(1-x^2)', 'arcsin(x)^2/2', {
  domain: D.unit,
  hints: ['$u=\\arcsin x$ 로 둔다.', '$du=\\dfrac{dx}{\\sqrt{1-x^{2}}}$'],
  steps: ['$u=\\arcsin x$', '$\\int u\\,du=\\dfrac{\\arcsin^{2}x}{2}$']
});
add('hard', '치환적분', 'ln(tan(x))/(sin(x)*cos(x))', 'ln(tan(x))^2/2', {
  domain: [0.3, 1.2],
  hints: ['$\\dfrac{1}{\\sin x\\cos x}=\\dfrac{\\sec^{2}x}{\\tan x}$ 로 바꾼다.', '$u=\\ln\\tan x$ 로 두면 $du=\\dfrac{\\sec^{2}x}{\\tan x}dx$ 다.'],
  steps: ['$u=\\ln\\tan x,\;du=\\dfrac{dx}{\\sin x\\cos x}$', '$\\int u\\,du=\\dfrac{\\ln^{2}\\tan x}{2}$']
});
add('medium', '치환적분', 'x^2/(1+x^6)', 'arctan(x^3)/3', {
  domain: D.poly,
  hints: ['$x^{6}=(x^{3})^{2}$ 임을 본다.', '$u=x^{3},\;du=3x^{2}dx$'],
  steps: ['$u=x^{3}$', '$\\dfrac13\\int\\dfrac{du}{1+u^{2}}=\\dfrac{\\arctan(x^{3})}{3}$']
});
add('hard', '지수 치환', '(2*x^2+1)*e^(x^2)', 'x*e^(x^2)', {
  domain: [0.2, 1.6],
  hints: ['$\\left(xe^{x^{2}}\\right)\'$ 를 계산해 본다.', '곱의 미분법에서 $e^{x^{2}}+2x^{2}e^{x^{2}}$ 가 나온다.'],
  steps: ['$\\left(xe^{x^{2}}\\right)\'=e^{x^{2}}+2x^{2}e^{x^{2}}=(2x^{2}+1)e^{x^{2}}$',
          '따라서 원시함수는 $xe^{x^{2}}$']
});
add('hard', '지수 치환', 'x^3*e^(x^2)', '(x^2-1)*e^(x^2)/2', {
  domain: [0.2, 1.6],
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\int ue^{u}du$ 다.', '$\\int ue^{u}du=(u-1)e^{u}$'],
  steps: ['$u=x^{2},\;du=2x\\,dx$', '$\\dfrac12\\int ue^{u}du=\\dfrac{(x^{2}-1)e^{x^{2}}}{2}$']
});
add('medium', '지수 밑 변환', 'x*2^x', '2^x*(x/ln(2)-1/ln(2)^2)', {
  domain: D.poly,
  hints: ['$2^{x}=e^{x\\ln 2}$ 로 바꾼다.', '$\\int 2^{x}dx=\\dfrac{2^{x}}{\\ln 2}$ 를 이용해 부분적분한다.'],
  steps: ['$\\int x2^{x}dx=\\dfrac{x2^{x}}{\\ln 2}-\\dfrac{1}{\\ln 2}\\int 2^{x}dx$',
          '$=2^{x}\\left(\\dfrac{x}{\\ln 2}-\\dfrac{1}{\\ln^{2}2}\\right)$']
});
add('hard', '지수 밑 변환', '2^x*e^x', '2^x*e^x/(1+ln(2))', {
  domain: [-1, 1.6],
  hints: ['$2^{x}e^{x}=(2e)^{x}$ 로 묶는다.', '$\\int a^{x}dx=\\dfrac{a^{x}}{\\ln a}$, 여기서 $\\ln(2e)=1+\\ln 2$'],
  steps: ['$2^{x}e^{x}=(2e)^{x}$', '$\\int(2e)^{x}dx=\\dfrac{(2e)^{x}}{\\ln(2e)}=\\dfrac{2^{x}e^{x}}{1+\\ln 2}$']
});
add('hard', '로그 치환', '2*ln(x)*x^(ln(x))/x', 'x^(ln(x))', {
  domain: [0.4, 2.6],
  hints: ['$x^{\\ln x}=e^{\\ln^{2}x}$ 로 쓴다.', '$\\left(\\ln^{2}x\\right)\'=\\dfrac{2\\ln x}{x}$'],
  steps: ['$y=x^{\\ln x}=e^{\\ln^{2}x}$', '$y\'=e^{\\ln^{2}x}\\cdot\\dfrac{2\\ln x}{x}$',
          '따라서 원시함수는 $x^{\\ln x}$']
});
add('hard', '로그 치환', 'ln(x)/(x*(1+ln(x))^2)', 'ln(1+ln(x))+1/(1+ln(x))', {
  domain: [1.2, 4.0],
  hints: ['$u=\\ln x$ 로 두면 $\\int\\dfrac{u}{(1+u)^{2}}du$ 다.', '$\\dfrac{u}{(1+u)^{2}}=\\dfrac{1}{1+u}-\\dfrac{1}{(1+u)^{2}}$'],
  steps: ['$u=\\ln x$', '$\\int\\left(\\dfrac{1}{1+u}-\\dfrac{1}{(1+u)^{2}}\\right)du=\\ln(1+u)+\\dfrac{1}{1+u}$']
});
add('hard', '부분적분', 'ln(x)/(1+x)^2', 'ln(x)-ln(1+x)-ln(x)/(1+x)', {
  domain: D.pos,
  hints: ['$v=-\\dfrac{1}{1+x}$ 로 부분적분한다.', '남는 $\\int\\dfrac{dx}{x(1+x)}$ 는 부분분수다.'],
  steps: ['$=-\\dfrac{\\ln x}{1+x}+\\int\\dfrac{dx}{x(1+x)}$',
          '$\\int\\dfrac{dx}{x(1+x)}=\\ln\\dfrac{x}{1+x}$']
});
add('hard', '부분적분', 'ln(1+x)/x^2', 'ln(x)-ln(1+x)-ln(1+x)/x', {
  domain: D.pos,
  hints: ['$v=-\\dfrac1x$ 로 부분적분한다.', '남는 적분은 $\\int\\dfrac{dx}{x(1+x)}$ 다.'],
  steps: ['$=-\\dfrac{\\ln(1+x)}{x}+\\int\\dfrac{dx}{x(1+x)}$', '$=\\ln\\dfrac{x}{1+x}-\\dfrac{\\ln(1+x)}{x}$']
});
add('hard', '부분적분', 'arctan(x)/x^2', 'ln(x)-ln(1+x^2)/2-arctan(x)/x', {
  domain: D.pos,
  hints: ['$v=-\\dfrac1x$ 로 부분적분한다.', '남는 적분 $\\int\\dfrac{dx}{x(1+x^{2})}$ 을 부분분수로 쪼갠다.'],
  steps: ['$=-\\dfrac{\\arctan x}{x}+\\int\\dfrac{dx}{x(1+x^{2})}$',
          '$\\dfrac{1}{x(1+x^{2})}=\\dfrac1x-\\dfrac{x}{1+x^{2}}$']
});
add('hard', '부분적분', 'ln(1+x^2)', 'x*ln(1+x^2)-2*x+2*arctan(x)', {
  domain: D.poly,
  hints: ['$dv=dx$ 로 부분적분하면 $\\int\\dfrac{2x^{2}}{1+x^{2}}dx$ 가 남는다.',
          '$\\dfrac{2x^{2}}{1+x^{2}}=2-\\dfrac{2}{1+x^{2}}$'],
  steps: ['$=x\\ln(1+x^{2})-\\int\\dfrac{2x^{2}}{1+x^{2}}dx$', '$=x\\ln(1+x^{2})-2x+2\\arctan x$']
});
add('hard', '부분적분', 'x*arcsin(x)', '(2*x^2-1)*arcsin(x)/4+x*sqrt(1-x^2)/4', {
  domain: D.unit,
  hints: ['$v=\\dfrac{x^{2}}{2}-\\dfrac14$ 로 잡으면 남는 적분이 쉬워진다.',
          '$\\int\\dfrac{2x^{2}-1}{4\\sqrt{1-x^{2}}}dx=-\\dfrac{x\\sqrt{1-x^{2}}}{4}$'],
  steps: ['$v=\\dfrac{2x^{2}-1}{4}$ 로 부분적분',
          '$=\\dfrac{(2x^{2}-1)\\arcsin x}{4}+\\dfrac{x\\sqrt{1-x^{2}}}{4}$']
});
add('hard', '부분적분', 'arcsin(x)^2', 'x*arcsin(x)^2+2*sqrt(1-x^2)*arcsin(x)-2*x', {
  domain: D.unit,
  hints: ['부분적분 후 $\\int\\dfrac{2x\\arcsin x}{\\sqrt{1-x^{2}}}dx$ 가 남는다.',
          '$\\left(-2\\sqrt{1-x^{2}}\\right)\'=\\dfrac{2x}{\\sqrt{1-x^{2}}}$ 로 한 번 더 부분적분한다.'],
  steps: ['$=x\\arcsin^{2}x-\\int\\dfrac{2x\\arcsin x}{\\sqrt{1-x^{2}}}dx$',
          '$=x\\arcsin^{2}x+2\\sqrt{1-x^{2}}\\arcsin x-2x$']
});
add('hard', '부분적분', 'sqrt(x)*ln(x)', '2*x^(3/2)*(3*ln(x)-2)/9', {
  domain: D.pos,
  hints: ['$dv=x^{1/2}dx\\Rightarrow v=\\dfrac{2}{3}x^{3/2}$', '남는 적분은 $\\dfrac23\\int x^{1/2}dx$ 다.'],
  steps: ['$=\\dfrac{2x^{3/2}\\ln x}{3}-\\dfrac23\\int x^{1/2}dx$', '$=\\dfrac{2x^{3/2}(3\\ln x-2)}{9}$']
});
add('hard', '부분적분', 'x^2*arctan(x)', 'x^3*arctan(x)/3-x^2/6+ln(1+x^2)/6', {
  domain: D.poly,
  hints: ['$v=\\dfrac{x^{3}}{3}$ 로 부분적분한다.', '$\\dfrac{x^{3}}{1+x^{2}}=x-\\dfrac{x}{1+x^{2}}$ 로 나눈다.'],
  steps: ['$=\\dfrac{x^{3}\\arctan x}{3}-\\dfrac13\\int\\dfrac{x^{3}}{1+x^{2}}dx$',
          '$=\\dfrac{x^{3}\\arctan x}{3}-\\dfrac{x^{2}}{6}+\\dfrac{\\ln(1+x^{2})}{6}$']
});
add('hard', '삼각·쌍곡 혼합', 'sin(x)*sinh(x)', '(sin(x)*cosh(x)-cos(x)*sinh(x))/2', {
  domain: [0.2, 2.0],
  hints: ['부분적분을 두 번 하면 원래 적분이 부호를 바꿔 돌아온다.', '$e^{x}\\sin x$ 와 같은 순환 구조다.'],
  steps: ['두 번 부분적분하면 $I=\\sin x\\cosh x-\\cos x\\sinh x-I$',
          '$I=\\dfrac{\\sin x\\cosh x-\\cos x\\sinh x}{2}$']
});
add('hard', '삼각 항등식', 'cos(2*x)/(cos(x)+sin(x))', 'sin(x)+cos(x)', {
  domain: D.trigW,
  hints: ['$\\cos 2x=\\cos^{2}x-\\sin^{2}x$ 를 인수분해한다.', '$(\\cos x-\\sin x)(\\cos x+\\sin x)$ 에서 분모가 약분된다.'],
  steps: ['$\\dfrac{\\cos 2x}{\\cos x+\\sin x}=\\cos x-\\sin x$', '$=\\sin x+\\cos x$']
});
add('hard', '쌍곡선함수', '1/cosh(x)', 'arctan(sinh(x))', {
  domain: [-1.4, 1.6],
  hints: ['분자·분모에 $\\cosh x$ 를 곱한다.', '$u=\\sinh x$ 로 두면 $\\cosh^{2}=1+\\sinh^{2}$ 다.'],
  steps: ['$\\dfrac{1}{\\cosh x}=\\dfrac{\\cosh x}{1+\\sinh^{2}x}$', '$u=\\sinh x:\;\\arctan(\\sinh x)$']
});
add('hard', '지수 삼각', 'e^(2*x)*sin(3*x)', 'e^(2*x)*(2*sin(3*x)-3*cos(3*x))/13', {
  domain: [0.15, 1.0],
  hints: ['$\\int e^{ax}\\sin bx\\,dx=\\dfrac{e^{ax}(a\\sin bx-b\\cos bx)}{a^{2}+b^{2}}$',
          '$a=2,\;b=3$ 이므로 분모가 $13$ 이다.'],
  steps: ['두 번 부분적분해 $I$ 를 정리하면',
          '$I=\\dfrac{e^{2x}(2\\sin 3x-3\\cos 3x)}{13}$']
});

// ================================================================== 몬스터 추가분 2

add('monster', '함정 문제', '((x-1)^(ln(x+1)))/((x+1)^(ln(x-1)))', 'x', {
  domain: [1.4, 3.4],
  hints: ['$a^{\\ln b}=e^{\\ln a\\ln b}=b^{\\ln a}$ 라는 사실을 쓴다.', '분자와 분모가 정확히 같은 값이다.'],
  steps: ['$(x-1)^{\\ln(x+1)}=e^{\\ln(x-1)\\ln(x+1)}=(x+1)^{\\ln(x-1)}$',
          '피적분함수는 $1$', '$\\int 1\\,dx=x$']
});
add('monster', '로그 중첩 치환', '1/(x*ln(x)+2*x)', 'ln(ln(x)+2)', {
  domain: [1.2, 4.0],
  hints: ['분모를 $x(\\ln x+2)$ 로 묶는다.', '$u=\\ln x+2$ 로 두면 $du=\\dfrac{dx}{x}$ 다.'],
  steps: ['$\\dfrac{1}{x(\\ln x+2)}$', '$u=\\ln x+2$', '$\\int\\dfrac{du}{u}=\\ln|\\ln x+2|$']
});
add('monster', '로그 중첩 치환', '1/(x*ln(x)*ln(ln(x)))', 'ln(ln(ln(x)))', {
  domain: [17, 60],
  hints: ['안쪽부터 차례로 치환한다: $u=\\ln x$, 다음 $v=\\ln u$.', '$\\ln\\ln\\ln x$ 가 정의되려면 $x>e^{e}$ 여야 한다.'],
  steps: ['$u=\\ln x:\;\\int\\dfrac{du}{u\\ln u}$', '$v=\\ln u:\;\\int\\dfrac{dv}{v}=\\ln v$',
          '$=\\ln\\ln\\ln x$']
});
add('monster', '지수탑 미분', 'x^x*(1+ln(x))', 'x^x', {
  domain: [0.4, 2.2],
  hints: ['$x^{x}=e^{x\\ln x}$ 로 쓴다.', '$(x\\ln x)\'=\\ln x+1$ 이므로 통째로 치환이 된다.'],
  steps: ['$y=x^{x}=e^{x\\ln x}$', '$y\'=e^{x\\ln x}(\\ln x+1)=x^{x}(1+\\ln x)$',
          '따라서 원시함수는 $x^{x}$']
});
add('monster', '역수 치환', '(x^2-1)*e^(x+1/x)/x^2', 'e^(x+1/x)', {
  domain: [0.4, 2.4],
  hints: ['$\\dfrac{x^{2}-1}{x^{2}}=1-\\dfrac{1}{x^{2}}$ 로 쪼갠다.',
          '$u=x+\\dfrac1x$ 의 도함수가 바로 그것이다.'],
  steps: ['$u=x+\\dfrac1x,\;du=\\left(1-\\dfrac{1}{x^{2}}\\right)dx$',
          '$\\int e^{u}du=e^{x+1/x}$']
});
add('monster', '곱의 미분 되짚기', '(1+x)/(x*(1+x*e^x))', 'ln(x*e^x)-ln(1+x*e^x)', {
  domain: [0.3, 2.2], lnAbs: true,
  hints: ['분자·분모에 $e^{x}$ 를 곱하면 $w=xe^{x}$ 의 미분 $\\ (1+x)e^{x}$ 가 보인다.',
          '$\\dfrac{1}{w(1+w)}=\\dfrac1w-\\dfrac{1}{1+w}$'],
  steps: ['$\\dfrac{(1+x)e^{x}}{xe^{x}(1+xe^{x})}$, $w=xe^{x}$',
          '$\\int\\dfrac{dw}{w(1+w)}=\\ln\\left|\\dfrac{w}{1+w}\\right|=\\ln\\left|\\dfrac{xe^{x}}{1+xe^{x}}\\right|$']
});
add('monster', '반각 치환', 'e^x*(1+sin(x))/(1+cos(x))', 'e^x*tan(x/2)', {
  domain: [0.2, 2.2],
  hints: ['$\\dfrac{\\sin x}{1+\\cos x}=\\tan\\dfrac x2$, $\\dfrac{1}{1+\\cos x}=\\dfrac12\\sec^{2}\\dfrac x2$ 로 쪼갠다.',
          '$\\int e^{x}(f+f\')dx=e^{x}f$ 꼴이 된다.'],
  steps: ['$\\dfrac{1+\\sin x}{1+\\cos x}=\\tan\\dfrac x2+\\dfrac12\\sec^{2}\\dfrac x2$',
          '$f=\\tan\\dfrac x2,\;f\'=\\dfrac12\\sec^{2}\\dfrac x2$', '$=e^{x}\\tan\\dfrac x2$']
});
add('monster', '삼각 유리식', 'sin(x)/(sin(x)+cos(x))', 'x/2-ln(sin(x)+cos(x))/2', {
  domain: [0.2, 2.2], lnAbs: true,
  hints: ['$\\sin x=\\dfrac{(\\sin+\\cos)-(\\cos-\\sin)}{2}$ 로 쪼갠다.',
          '$(\\sin x+\\cos x)\'=\\cos x-\\sin x$ 이므로 뒤 항이 로그가 된다.'],
  steps: ['$\\dfrac{\\sin x}{\\sin x+\\cos x}=\\dfrac12-\\dfrac12\\cdot\\dfrac{\\cos x-\\sin x}{\\sin x+\\cos x}$',
          '$=\\dfrac x2-\\dfrac12\\ln|\\sin x+\\cos x|$']
});
add('monster', '삼각 유리식', '1/(1+tan(x))', 'x/2+ln(sin(x)+cos(x))/2', {
  domain: D.trig, lnAbs: true,
  hints: ['$\\dfrac{1}{1+\\tan x}=\\dfrac{\\cos x}{\\cos x+\\sin x}$ 로 바꾼다.',
          '$\\cos x=\\dfrac{(\\cos+\\sin)+(\\cos-\\sin)}{2}$ 로 쪼갠다.'],
  steps: ['$\\dfrac{\\cos x}{\\sin x+\\cos x}=\\dfrac12+\\dfrac12\\cdot\\dfrac{\\cos x-\\sin x}{\\sin x+\\cos x}$',
          '$=\\dfrac x2+\\dfrac12\\ln|\\sin x+\\cos x|$']
});
add('monster', '삼각 유리식', '1/(sin(x)+cos(x))', 'ln(tan(x/2+pi/8))/sqrt(2)', {
  domain: [0.3, 1.6], lnAbs: true,
  hints: ['$\\sin x+\\cos x=\\sqrt2\\sin\\left(x+\\dfrac\\pi4\\right)$ 로 합성한다.',
          '$\\int\\csc t\\,dt=\\ln\\left|\\tan\\dfrac t2\\right|$'],
  steps: ['$\\dfrac{1}{\\sqrt2}\\int\\csc\\left(x+\\dfrac\\pi4\\right)dx$',
          '$=\\dfrac{1}{\\sqrt2}\\ln\\left|\\tan\\left(\\dfrac x2+\\dfrac\\pi8\\right)\\right|$']
});
add('monster', '적분대회 고전', 'sqrt(tan(x))+sqrt(cot(x))', 'sqrt(2)*arcsin(sin(x)-cos(x))', {
  domain: [0.3, 1.2],
  hints: ['통분하면 $\\dfrac{\\sin x+\\cos x}{\\sqrt{\\sin x\\cos x}}$ 다.',
          '$u=\\sin x-\\cos x$ 로 두면 $u^{2}=1-2\\sin x\\cos x$ 다.'],
  steps: ['$\\sqrt{\\tan x}+\\sqrt{\\cot x}=\\dfrac{\\sin x+\\cos x}{\\sqrt{\\sin x\\cos x}}$',
          '$u=\\sin x-\\cos x,\;\\sin x\\cos x=\\dfrac{1-u^{2}}{2}$',
          '$\\sqrt2\\int\\dfrac{du}{\\sqrt{1-u^{2}}}=\\sqrt2\\arcsin(\\sin x-\\cos x)$']
});
add('monster', '적분대회 고전', 'sqrt(tan(x))',
    'ln((tan(x)-sqrt(2)*sqrt(tan(x))+1)/(tan(x)+sqrt(2)*sqrt(tan(x))+1))/(2*sqrt(2))'
  + '+(arctan(sqrt(2)*sqrt(tan(x))+1)+arctan(sqrt(2)*sqrt(tan(x))-1))/sqrt(2)', {
  domain: [0.3, 1.2],
  hints: ['$t=\\sqrt{\\tan x}$ 로 두면 $dx=\\dfrac{2t\\,dt}{1+t^{4}}$ 다.',
          '$\\int\\dfrac{2t^{2}}{1+t^{4}}dt$ 는 $t^{2}\\pm1$ 로 쪼개는 4차 유리식 문제가 된다.'],
  steps: ['$t=\\sqrt{\\tan x},\;dx=\\dfrac{2t\\,dt}{1+t^{4}}$',
          '$\\int\\dfrac{2t^{2}}{1+t^{4}}dt=\\int\\dfrac{t^{2}+1}{t^{4}+1}dt+\\int\\dfrac{t^{2}-1}{t^{4}+1}dt$',
          '각각 $u=t\\mp\\dfrac1t$ 치환으로 $\\arctan$ 항과 로그 항을 얻는다']
});
add('monster', '4차 유리식', '(x^2+1)/(x^4+x^2+1)', 'arctan((x^2-1)/(sqrt(3)*x))/sqrt(3)', {
  domain: [0.25, 2.6],
  hints: ['분자·분모를 $x^{2}$ 로 나눈다.', '$u=x-\\dfrac1x$ 로 두면 분모가 $u^{2}+3$ 이다.'],
  steps: ['$\\dfrac{1+x^{-2}}{x^{2}+1+x^{-2}}$', '$u=x-\\dfrac1x,\;x^{2}+x^{-2}=u^{2}+2$',
          '$\\int\\dfrac{du}{u^{2}+3}=\\dfrac{1}{\\sqrt3}\\arctan\\dfrac{u}{\\sqrt3}$']
});
add('monster', '4차 유리식', '(x^2-1)/(x^4+x^2+1)', 'ln((x^2-x+1)/(x^2+x+1))/2', {
  domain: [0.25, 2.6],
  hints: ['이번엔 $u=x+\\dfrac1x$ 로 두면 분모가 $u^{2}-1$ 이다.',
          '$\\int\\dfrac{du}{u^{2}-1}=\\dfrac12\\ln\\left|\\dfrac{u-1}{u+1}\\right|$'],
  steps: ['$\\dfrac{1-x^{-2}}{x^{2}+1+x^{-2}}$', '$u=x+\\dfrac1x$',
          '$\\dfrac12\\ln\\left|\\dfrac{x^{2}-x+1}{x^{2}+x+1}\\right|$']
});
add('monster', '4차 유리식', '1/(x^4+x^2+1)',
    'arctan((x^2-1)/(sqrt(3)*x))/(2*sqrt(3))-ln((x^2-x+1)/(x^2+x+1))/4', {
  domain: [0.25, 2.6],
  hints: ['$1=\\dfrac{(x^{2}+1)-(x^{2}-1)}{2}$ 로 쪼개면 앞의 두 문제로 환원된다.',
          '$x^{4}+x^{2}+1=(x^{2}-x+1)(x^{2}+x+1)$'],
  steps: ['$\\dfrac{1}{x^{4}+x^{2}+1}=\\dfrac12\\cdot\\dfrac{x^{2}+1}{x^{4}+x^{2}+1}-\\dfrac12\\cdot\\dfrac{x^{2}-1}{x^{4}+x^{2}+1}$',
          '두 결과를 대입한다']
});
add('monster', '4차 유리식', 'x^2/(x^4+x^2+1)',
    'arctan((x^2-1)/(sqrt(3)*x))/(2*sqrt(3))+ln((x^2-x+1)/(x^2+x+1))/4', {
  domain: [0.25, 2.6],
  hints: ['$x^{2}=\\dfrac{(x^{2}+1)+(x^{2}-1)}{2}$ 로 쪼갠다.', '$\\dfrac{1}{x^{4}+x^{2}+1}$ 과 부호 하나만 다르다.'],
  steps: ['$\\dfrac{x^{2}}{x^{4}+x^{2}+1}=\\dfrac12\\left(\\dfrac{x^{2}+1}{x^{4}+x^{2}+1}+\\dfrac{x^{2}-1}{x^{4}+x^{2}+1}\\right)$',
          '두 결과를 더한다']
});
add('monster', '4차 유리식', '1/(x^4+4)',
    'ln((x^2+2*x+2)/(x^2-2*x+2))/16+(arctan(x-1)+arctan(x+1))/8', {
  domain: [0.2, 2.6],
  hints: ['소피 제르맹 항등식 $x^{4}+4=(x^{2}-2x+2)(x^{2}+2x+2)$ 를 쓴다.',
          '각 이차식은 $(x\\mp1)^{2}+1$ 로 완전제곱된다.'],
  steps: ['$x^{4}+4=(x^{2}-2x+2)(x^{2}+2x+2)$',
          '부분분수로 쪼개면 로그 항과 $\\arctan$ 항이 나온다',
          '$=\\dfrac{1}{16}\\ln\\dfrac{x^{2}+2x+2}{x^{2}-2x+2}+\\dfrac{\\arctan(x-1)+\\arctan(x+1)}{8}$']
});
add('monster', '6차 유리식', '1/(x^6+1)',
    'arctan(x)/3+arctan((x^2-1)/x)/6-sqrt(3)*ln((x^2-sqrt(3)*x+1)/(x^2+sqrt(3)*x+1))/12', {
  domain: [0.25, 2.6],
  hints: ['$x^{6}+1=(x^{2}+1)(x^{4}-x^{2}+1)$ 로 인수분해한다.',
          '$\\dfrac{1}{x^{6}+1}=\\dfrac13\\cdot\\dfrac{1}{x^{2}+1}+\\dfrac13\\cdot\\dfrac{2-x^{2}}{x^{4}-x^{2}+1}$'],
  steps: ['$2-x^{2}=\\dfrac{(x^{2}+1)}{2}-\\dfrac{3(x^{2}-1)}{2}$ 로 다시 쪼갠다',
          '$u=x-\\dfrac1x$ 와 $u=x+\\dfrac1x$ 치환을 각각 쓴다',
          '$\\arctan$ 두 항과 로그 한 항이 남는다']
});
add('monster', '역수 치환', '(x^2-1)/((x^2+1)*sqrt(x^4+1))',
    'arctan(sqrt(x^4+1)/(sqrt(2)*x))/sqrt(2)', {
  domain: [0.3, 2.6],
  hints: ['분자·분모를 $x^{2}$ 로 나누면 $\\dfrac{1-x^{-2}}{(x+x^{-1})\\sqrt{x^{2}+x^{-2}}}$ 다.',
          '$u=x+\\dfrac1x$ 로 두면 $x^{2}+x^{-2}=u^{2}-2$ 다.'],
  steps: ['$u=x+\\dfrac1x,\;du=\\left(1-\\dfrac{1}{x^{2}}\\right)dx$',
          '$\\int\\dfrac{du}{u\\sqrt{u^{2}-2}}=\\dfrac{1}{\\sqrt2}\\arctan\\dfrac{\\sqrt{u^{2}-2}}{\\sqrt2}$',
          '$\\sqrt{u^{2}-2}=\\dfrac{\\sqrt{x^{4}+1}}{x}$']
});
add('monster', '3차 유리식', '1/(1+x^3)',
    'ln(x+1)/3-ln(x^2-x+1)/6+arctan((2*x-1)/sqrt(3))/sqrt(3)', {
  domain: [0.2, 2.4], lnAbs: true,
  hints: ['$1+x^{3}=(x+1)(x^{2}-x+1)$ 로 인수분해한 뒤 부분분수를 쓴다.',
          '$\\dfrac{1}{1+x^{3}}=\\dfrac{1}{3(x+1)}+\\dfrac{2-x}{3(x^{2}-x+1)}$'],
  steps: ['부분분수로 쪼갠다',
          '$x^{2}-x+1=\\left(x-\\dfrac12\\right)^{2}+\\dfrac34$ 로 완전제곱',
          '로그 항과 $\\arctan$ 항이 나온다']
});
add('monster', '분수 지수 치환', '1/(sqrt(x)+x^(1/3))',
    '2*sqrt(x)-3*x^(1/3)+6*x^(1/6)-6*ln(x^(1/6)+1)', {
  domain: [0.3, 3.0],
  hints: ['지수의 분모 $2,3$ 의 최소공배수를 보고 $u=x^{1/6}$ 로 둔다.', '$dx=6u^{5}du$ 를 대입하면 다항식 나눗셈만 남는다.'],
  steps: ['$u=x^{1/6},\;dx=6u^{5}du$', '$\\int\\dfrac{6u^{5}}{u^{3}+u^{2}}du=6\\int\\dfrac{u^{3}}{u+1}du$',
          '$=2u^{3}-3u^{2}+6u-6\\ln(u+1)$']
});

// ================================================================== 어려움/몬스터 추가분 3

add('hard', '완전제곱', '(2*x+3)/sqrt(x^2+4*x+13)', '2*sqrt(x^2+4*x+13)-asinh((x+2)/3)', {
  domain: [0.2, 3.0],
  hints: ['분자를 $(2x+4)-1$ 로 쪼갠다.', '$x^{2}+4x+13=(x+2)^{2}+9$ 로 완전제곱한다.'],
  steps: ['$\\int\\dfrac{2x+4}{\\sqrt{x^{2}+4x+13}}dx=2\\sqrt{x^{2}+4x+13}$',
          '$\\int\\dfrac{dx}{\\sqrt{(x+2)^{2}+9}}=\\operatorname{arsinh}\\dfrac{x+2}{3}$']
});
add('hard', '완전제곱', 'x/sqrt(x^2+2*x+5)', 'sqrt(x^2+2*x+5)-asinh((x+1)/2)', {
  domain: [0.2, 3.0],
  hints: ['분자를 $\\dfrac{(2x+2)}{2}-1$ 로 쪼갠다.', '$x^{2}+2x+5=(x+1)^{2}+4$'],
  steps: ['$\\dfrac12\\int\\dfrac{2x+2}{\\sqrt{\\cdot}}dx=\\sqrt{x^{2}+2x+5}$',
          '$-\\int\\dfrac{dx}{\\sqrt{(x+1)^{2}+4}}=-\\operatorname{arsinh}\\dfrac{x+1}{2}$']
});
add('hard', '삼각 치환', '1/(1+x^2)^(3/2)', 'x/sqrt(1+x^2)', {
  domain: [-1.5, 1.7],
  hints: ['$x=\\tan\\theta$ 로 두면 $\\int\\cos\\theta\\,d\\theta$ 다.', '$\\sin\\theta=\\dfrac{x}{\\sqrt{1+x^{2}}}$'],
  steps: ['$x=\\tan\\theta,\;dx=\\sec^{2}\\theta\\,d\\theta$', '$\\int\\cos\\theta\\,d\\theta=\\dfrac{x}{\\sqrt{1+x^{2}}}$']
});
add('hard', '삼각 치환', '1/(1-x^2)^(3/2)', 'x/sqrt(1-x^2)', {
  domain: D.unit,
  hints: ['$x=\\sin\\theta$ 로 두면 $\\int\\sec^{2}\\theta\\,d\\theta$ 다.', '$\\tan\\theta=\\dfrac{x}{\\sqrt{1-x^{2}}}$'],
  steps: ['$x=\\sin\\theta$', '$\\int\\sec^{2}\\theta\\,d\\theta=\\tan\\theta=\\dfrac{x}{\\sqrt{1-x^{2}}}$']
});
add('hard', '삼각 치환', '1/(x^2*sqrt(x^2+1))', '-sqrt(x^2+1)/x', {
  domain: D.pos,
  hints: ['$x=\\tan\\theta$ 로 두면 $\\int\\dfrac{\\cos\\theta}{\\sin^{2}\\theta}d\\theta$ 다.', '$-\\csc\\theta=-\\dfrac{\\sqrt{x^{2}+1}}{x}$'],
  steps: ['$x=\\tan\\theta$', '$\\int\\csc\\theta\\cot\\theta\\,d\\theta=-\\csc\\theta$',
          '$=-\\dfrac{\\sqrt{x^{2}+1}}{x}$']
});
add('medium', '삼각 치환', 'x^2/sqrt(1-x^2)', 'arcsin(x)/2-x*sqrt(1-x^2)/2', {
  domain: D.unit,
  hints: ['$x=\\sin\\theta$ 로 두면 $\\int\\sin^{2}\\theta\\,d\\theta$ 다.', '반각공식으로 내린다.'],
  steps: ['$\\int\\sin^{2}\\theta\\,d\\theta=\\dfrac{\\theta}{2}-\\dfrac{\\sin 2\\theta}{4}$',
          '$=\\dfrac{\\arcsin x}{2}-\\dfrac{x\\sqrt{1-x^{2}}}{2}$']
});
add('medium', '치환적분', 'x^3/sqrt(1-x^2)', '(1-x^2)^(3/2)/3-sqrt(1-x^2)', {
  domain: D.unit,
  hints: ['$u=1-x^{2}$ 로 두고 $x^{2}=1-u$ 를 대입한다.', '$-\\dfrac12\\int\\dfrac{1-u}{\\sqrt u}du$'],
  steps: ['$u=1-x^{2}$', '$-\\dfrac12\\int(u^{-1/2}-u^{1/2})du=\\dfrac{u^{3/2}}{3}-u^{1/2}$']
});
add('medium', '치환적분', 'sqrt(x)/(1+x)', '2*sqrt(x)-2*arctan(sqrt(x))', {
  domain: D.pos,
  hints: ['$u=\\sqrt x$ 로 두면 $2\\int\\dfrac{u^{2}}{1+u^{2}}du$ 다.', '$\\dfrac{u^{2}}{1+u^{2}}=1-\\dfrac{1}{1+u^{2}}$'],
  steps: ['$u=\\sqrt x,\;dx=2u\\,du$', '$2\\int\\left(1-\\dfrac{1}{1+u^{2}}\\right)du=2\\sqrt x-2\\arctan\\sqrt x$']
});
add('medium', '치환적분', 'ln(x)/sqrt(x)', '2*sqrt(x)*(ln(x)-2)', {
  domain: D.pos,
  hints: ['$dv=x^{-1/2}dx\\Rightarrow v=2\\sqrt x$ 로 부분적분한다.', '남는 적분은 $2\\int x^{-1/2}dx$ 다.'],
  steps: ['$=2\\sqrt x\\ln x-2\\int\\dfrac{dx}{\\sqrt x}$', '$=2\\sqrt x(\\ln x-2)$']
});
add('medium', '치환적분', 'ln(x)^2/x^2', '-(ln(x)^2+2*ln(x)+2)/x', {
  domain: D.pos,
  hints: ['$v=-\\dfrac1x$ 로 부분적분을 두 번 한다.', '$\\int\\dfrac{\\ln x}{x^{2}}dx=-\\dfrac{\\ln x+1}{x}$ 를 재활용한다.'],
  steps: ['$=-\\dfrac{\\ln^{2}x}{x}+2\\int\\dfrac{\\ln x}{x^{2}}dx$',
          '$=-\\dfrac{\\ln^{2}x+2\\ln x+2}{x}$']
});
add('medium', '치환적분', 'cos(x)*ln(sin(x))', 'sin(x)*(ln(sin(x))-1)', {
  domain: [0.3, 2.2],
  hints: ['$u=\\sin x$ 로 두면 $\\int\\ln u\\,du$ 다.', '$\\int\\ln u\\,du=u\\ln u-u$'],
  steps: ['$u=\\sin x$', '$\\int\\ln u\\,du=u(\\ln u-1)=\\sin x(\\ln\\sin x-1)$']
});
add('hard', '역삼각 부분적분', 'arctan(1/x)', 'x*arctan(1/x)+ln(1+x^2)/2', {
  domain: D.pos,
  hints: ['$dv=dx$ 로 부분적분한다.', '$\\left(\\arctan\\dfrac1x\\right)\'=-\\dfrac{1}{1+x^{2}}$'],
  steps: ['$=x\\arctan\\dfrac1x+\\int\\dfrac{x}{1+x^{2}}dx$', '$=x\\arctan\\dfrac1x+\\dfrac{\\ln(1+x^{2})}{2}$']
});
add('hard', '부분분수', '(x+1)/((x^2+1)*(x-1))', 'ln(x-1)-ln(x^2+1)/2', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['$\\dfrac{x+1}{(x-1)(x^{2}+1)}=\\dfrac{1}{x-1}-\\dfrac{x}{x^{2}+1}$', '가리기(cover-up)로 $x=1$ 을 넣으면 계수 $1$ 이 나온다.'],
  steps: ['부분분수로 쪼갠다', '$=\\ln|x-1|-\\dfrac12\\ln(x^{2}+1)$']
});
add('hard', '쌍곡선함수', 'tanh(x)^2', 'x-tanh(x)', {
  domain: [0.2, 2.0],
  hints: ['$\\tanh^{2}=1-\\operatorname{sech}^{2}$ 를 쓴다.', '$\\int\\operatorname{sech}^{2}x\\,dx=\\tanh x$'],
  steps: ['$\\tanh^{2}x=1-\\operatorname{sech}^{2}x$', '$=x-\\tanh x$']
});
add('hard', '지수 치환', 'e^(e^x+x)', 'e^(e^x)', {
  domain: [-1.0, 1.0],
  hints: ['$e^{e^{x}+x}=e^{e^{x}}\\cdot e^{x}$ 로 분리한다.', '$u=e^{x}$ 로 두면 $\\int e^{u}du$ 다.'],
  steps: ['$e^{e^{x}+x}=e^{x}e^{e^{x}}$', '$u=e^{x}:\;\\int e^{u}du=e^{e^{x}}$']
});
add('hard', '미분 꼴 알아보기', 'e^x*(x-1)/(x+1)^3', 'e^x/(x+1)^2', {
  domain: [0.2, 2.4],
  hints: ['$f=\\dfrac{1}{(x+1)^{2}}$ 로 두고 $f\'$ 를 계산해 본다.', '$\\int e^{x}(f+f\')dx=e^{x}f$'],
  steps: ['$f=\\dfrac{1}{(x+1)^{2}},\;f\'=-\\dfrac{2}{(x+1)^{3}}$',
          '$f+f\'=\\dfrac{(x+1)-2}{(x+1)^{3}}=\\dfrac{x-1}{(x+1)^{3}}$', '$=\\dfrac{e^{x}}{(x+1)^{2}}$']
});
add('hard', '미분 꼴 알아보기', 'e^x*sec(x)*(1+tan(x))', 'e^x*sec(x)', {
  domain: D.trig,
  hints: ['$f=\\sec x$ 라 하면 $f\'=\\sec x\\tan x$ 다.', '$\\int e^{x}(f+f\')dx=e^{x}f$'],
  steps: ['$f=\\sec x,\;f\'=\\sec x\\tan x$', '$=e^{x}\\sec x$']
});
add('medium', '로그 치환', 'ln(ln(x))/x', 'ln(x)*ln(ln(x))-ln(x)', {
  domain: [1.4, 4.2],
  hints: ['$u=\\ln x$ 로 두면 $\\int\\ln u\\,du$ 다.', '$\\int\\ln u\\,du=u\\ln u-u$'],
  steps: ['$u=\\ln x,\;du=\\dfrac{dx}{x}$', '$\\int\\ln u\\,du=u\\ln u-u=\\ln x\\,\\ln\\ln x-\\ln x$']
});
add('medium', '로그 치환', 'ln(x)/(x*sqrt(1+ln(x)))', '2*(1+ln(x))^(3/2)/3-2*sqrt(1+ln(x))', {
  domain: [1.2, 4.0],
  hints: ['$u=1+\\ln x$ 로 두면 $\\int\\dfrac{u-1}{\\sqrt u}du$ 다.', '$\\dfrac{u-1}{\\sqrt u}=\\sqrt u-\\dfrac{1}{\\sqrt u}$'],
  steps: ['$u=1+\\ln x$', '$\\int(u^{1/2}-u^{-1/2})du=\\dfrac{2u^{3/2}}{3}-2u^{1/2}$']
});
add('medium', '치환적분', 'sin(2*x)/(1+sin(x)^4)', 'arctan(sin(x)^2)', {
  domain: [0.25, 1.3],
  hints: ['$\\sin 2x=2\\sin x\\cos x$ 이므로 $u=\\sin^{2}x$ 의 미분이 그대로 보인다.',
          '$\\int\\dfrac{du}{1+u^{2}}=\\arctan u$'],
  steps: ['$u=\\sin^{2}x,\;du=\\sin 2x\\,dx$', '$\\arctan(\\sin^{2}x)$']
});
add('hard', '치환적분', '1/(x*sqrt(x^2+1))', 'ln((sqrt(x^2+1)-1)/(sqrt(x^2+1)+1))/2', {
  domain: D.pos,
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\int\\dfrac{du}{u\\sqrt{u+1}}$ 다.',
          '다시 $s=\\sqrt{u+1}$ 로 두면 부분분수가 된다.'],
  steps: ['$s=\\sqrt{x^{2}+1}$', '$\\int\\dfrac{ds}{s^{2}-1}=\\dfrac12\\ln\\left|\\dfrac{s-1}{s+1}\\right|$']
});
add('hard', '분수 지수 치환', 'sqrt(1+sqrt(x))', '4*(1+sqrt(x))^(5/2)/5-4*(1+sqrt(x))^(3/2)/3', {
  domain: [0.3, 3.0],
  hints: ['$u=\\sqrt x$ 먼저, 그다음 $w=\\sqrt{1+u}$ 로 두 번 치환한다.', '$dx=2u\\,du$, $u=w^{2}-1$'],
  steps: ['$u=\\sqrt x:\;2\\int u\\sqrt{1+u}\\,du$', '$w=\\sqrt{1+u}:\;4\\int(w^{4}-w^{2})dw$',
          '$=\\dfrac{4w^{5}}{5}-\\dfrac{4w^{3}}{3}$']
});

add('monster', '4차 유리식', '(x^2+1)/(x^4-x^2+1)', 'arctan((x^2-1)/x)', {
  domain: [0.3, 2.6],
  hints: ['분자·분모를 $x^{2}$ 로 나눈다.', '$u=x-\\dfrac1x$ 로 두면 분모가 $u^{2}+1$ 이다.'],
  steps: ['$\\dfrac{1+x^{-2}}{x^{2}-1+x^{-2}}$', '$u=x-\\dfrac1x,\;x^{2}+x^{-2}=u^{2}+2$',
          '$\\int\\dfrac{du}{u^{2}+1}=\\arctan\\dfrac{x^{2}-1}{x}$']
});
add('monster', '4차 유리식', '(x^2-1)/(x^4-x^2+1)',
    'ln((x^2-sqrt(3)*x+1)/(x^2+sqrt(3)*x+1))/(2*sqrt(3))', {
  domain: [0.3, 2.6],
  hints: ['$u=x+\\dfrac1x$ 로 두면 분모가 $u^{2}-3$ 이다.',
          '$\\int\\dfrac{du}{u^{2}-3}=\\dfrac{1}{2\\sqrt3}\\ln\\left|\\dfrac{u-\\sqrt3}{u+\\sqrt3}\\right|$'],
  steps: ['$\\dfrac{1-x^{-2}}{x^{2}-1+x^{-2}}$', '$u=x+\\dfrac1x$',
          '$=\\dfrac{1}{2\\sqrt3}\\ln\\left|\\dfrac{x^{2}-\\sqrt3x+1}{x^{2}+\\sqrt3x+1}\\right|$']
});
add('monster', '4차 유리식', '1/(x^4-x^2+1)',
    'arctan((x^2-1)/x)/2-ln((x^2-sqrt(3)*x+1)/(x^2+sqrt(3)*x+1))/(4*sqrt(3))', {
  domain: [0.3, 2.6],
  hints: ['$1=\\dfrac{(x^{2}+1)-(x^{2}-1)}{2}$ 로 쪼갠다.', '앞의 두 문제 결과를 그대로 조합한다.'],
  steps: ['$\\dfrac{1}{x^{4}-x^{2}+1}=\\dfrac12\\cdot\\dfrac{x^{2}+1}{x^{4}-x^{2}+1}-\\dfrac12\\cdot\\dfrac{x^{2}-1}{x^{4}-x^{2}+1}$',
          '두 결과를 대입한다']
});
add('monster', '4차 유리식', 'x^2/(x^4-x^2+1)',
    'arctan((x^2-1)/x)/2+ln((x^2-sqrt(3)*x+1)/(x^2+sqrt(3)*x+1))/(4*sqrt(3))', {
  domain: [0.3, 2.6],
  hints: ['$x^{2}=\\dfrac{(x^{2}+1)+(x^{2}-1)}{2}$ 로 쪼갠다.', '부호 하나만 바뀐다.'],
  steps: ['두 기본 결과를 더한다', '$\\arctan$ 항과 로그 항이 같은 부호로 남는다']
});
add('monster', '3차 유리식', 'x/(1+x^3)',
    '-ln(x+1)/3+ln(x^2-x+1)/6+arctan((2*x-1)/sqrt(3))/sqrt(3)', {
  domain: [0.2, 2.4], lnAbs: true,
  hints: ['$\\dfrac{x}{1+x^{3}}=-\\dfrac{1}{3(x+1)}+\\dfrac{x+1}{3(x^{2}-x+1)}$',
          '두 번째 항은 $\\dfrac{2x-1}{2}$ 와 상수로 다시 쪼갠다.'],
  steps: ['부분분수로 쪼갠다',
          '$\\int\\dfrac{x+1}{x^{2}-x+1}dx=\\dfrac12\\ln(x^{2}-x+1)+\\sqrt3\\arctan\\dfrac{2x-1}{\\sqrt3}$']
});
add('monster', '3차 유리식', '1/(x^3-1)',
    'ln(x-1)/3-ln(x^2+x+1)/6-arctan((2*x+1)/sqrt(3))/sqrt(3)', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['$x^{3}-1=(x-1)(x^{2}+x+1)$ 로 인수분해한다.',
          '$\\dfrac{1}{x^{3}-1}=\\dfrac{1}{3(x-1)}-\\dfrac{x+2}{3(x^{2}+x+1)}$'],
  steps: ['부분분수로 쪼갠다', '$x^{2}+x+1=\\left(x+\\dfrac12\\right)^{2}+\\dfrac34$',
          '로그 항과 $\\arctan$ 항이 나온다']
});
add('monster', '적분대회 고전', 'sqrt(cot(x))',
    '-ln((cot(x)-sqrt(2)*sqrt(cot(x))+1)/(cot(x)+sqrt(2)*sqrt(cot(x))+1))/(2*sqrt(2))'
  + '-(arctan(sqrt(2)*sqrt(cot(x))+1)+arctan(sqrt(2)*sqrt(cot(x))-1))/sqrt(2)', {
  domain: [0.35, 1.2],
  hints: ['$t=\\sqrt{\\cot x}$ 로 두면 $dx=-\\dfrac{2t\\,dt}{1+t^{4}}$ 다.',
          '$\\sqrt{\\tan x}$ 문제와 부호만 반대다.'],
  steps: ['$t=\\sqrt{\\cot x}$', '$-\\int\\dfrac{2t^{2}}{1+t^{4}}dt$',
          '$\\sqrt{\\tan x}$ 의 결과에 $-$ 를 붙이고 $\\tan\\to\\cot$ 로 바꾼다']
});
add('monster', '삼각 유리식', '(sin(x)+cos(x))/sqrt(sin(2*x))', 'arcsin(sin(x)-cos(x))', {
  domain: [0.3, 1.25],
  hints: ['$u=\\sin x-\\cos x$ 로 두면 $du=(\\cos x+\\sin x)dx$ 다.', '$u^{2}=1-\\sin 2x$'],
  steps: ['$u=\\sin x-\\cos x,\;\\sin 2x=1-u^{2}$',
          '$\\int\\dfrac{du}{\\sqrt{1-u^{2}}}=\\arcsin(\\sin x-\\cos x)$']
});
add('monster', '삼각 유리식', '(sin(x)-cos(x))/sqrt(sin(2*x))', '-ln(sin(x)+cos(x)+sqrt(sin(2*x)))', {
  domain: [0.45, 1.12],
  hints: ['이번엔 $u=\\sin x+\\cos x$ 로 두면 $u^{2}=1+\\sin 2x$ 다.',
          '$-\\int\\dfrac{du}{\\sqrt{u^{2}-1}}=-\\operatorname{arcosh}u$'],
  steps: ['$u=\\sin x+\\cos x,\;du=(\\cos x-\\sin x)dx$',
          '$-\\int\\dfrac{du}{\\sqrt{u^{2}-1}}=-\\ln\\left(u+\\sqrt{u^{2}-1}\\right)$']
});
add('monster', '삼각 유리식', 'sin(2*x)/(sin(x)^4+cos(x)^4)', '-arctan(cos(2*x))', {
  domain: [0.25, 1.3],
  hints: ['$u=\\sin^{2}x$ 로 두면 분모가 $u^{2}+(1-u)^{2}=2u^{2}-2u+1$ 이다.',
          '$2u^{2}-2u+1=2\\left(u-\\dfrac12\\right)^{2}+\\dfrac12$ 로 완전제곱한다.'],
  steps: ['$u=\\sin^{2}x,\;du=\\sin 2x\\,dx$',
          '$\\int\\dfrac{du}{2u^{2}-2u+1}=\\arctan(2u-1)$',
          '$2\\sin^{2}x-1=-\\cos 2x$']
});
add('monster', '유리식 치환', '1/(x*sqrt(x^3+1))',
    'ln((sqrt(x^3+1)-1)/(sqrt(x^3+1)+1))/3', {
  domain: [0.35, 2.4],
  hints: ['분자·분모에 $x^{2}$ 를 곱해 $u=x^{3}$ 을 만든다.',
          '$s=\\sqrt{u+1}$ 로 다시 치환하면 $\\int\\dfrac{2\\,ds}{s^{2}-1}$ 이다.'],
  steps: ['$u=x^{3}:\;\\dfrac13\\int\\dfrac{du}{u\\sqrt{u+1}}$',
          '$s=\\sqrt{u+1}:\;\\dfrac23\\int\\dfrac{ds}{s^{2}-1}$',
          '$=\\dfrac13\\ln\\left|\\dfrac{\\sqrt{x^{3}+1}-1}{\\sqrt{x^{3}+1}+1}\\right|$']
});

// ================================================================== 어려움/몬스터 추가분 4

add('medium', '부분적분', 'x^2*ln(x)', 'x^3*(3*ln(x)-1)/9', {
  domain: D.pos,
  hints: ['$dv=x^{2}dx\\Rightarrow v=\\dfrac{x^{3}}{3}$', '남는 적분은 $\\dfrac13\\int x^{2}dx$ 다.'],
  steps: ['$=\\dfrac{x^{3}\\ln x}{3}-\\dfrac13\\int x^{2}dx$', '$=\\dfrac{x^{3}(3\\ln x-1)}{9}$']
});
add('medium', '부분적분', 'x^3*ln(x)', 'x^4*(4*ln(x)-1)/16', {
  domain: D.pos,
  hints: ['$v=\\dfrac{x^{4}}{4}$ 로 부분적분한다.', '$\\int x^{n}\\ln x\\,dx=\\dfrac{x^{n+1}}{n+1}\\left(\\ln x-\\dfrac{1}{n+1}\\right)$'],
  steps: ['$=\\dfrac{x^{4}\\ln x}{4}-\\dfrac14\\int x^{3}dx$', '$=\\dfrac{x^{4}(4\\ln x-1)}{16}$']
});
add('medium', '부분적분', 'x*ln(x)^2', 'x^2*ln(x)^2/2-x^2*ln(x)/2+x^2/4', {
  domain: D.pos,
  hints: ['$v=\\dfrac{x^{2}}{2}$ 로 부분적분하면 $\\int x\\ln x\\,dx$ 가 남는다.',
          '$\\int x\\ln x\\,dx=\\dfrac{x^{2}\\ln x}{2}-\\dfrac{x^{2}}{4}$'],
  steps: ['$=\\dfrac{x^{2}\\ln^{2}x}{2}-\\int x\\ln x\\,dx$',
          '$=\\dfrac{x^{2}\\ln^{2}x}{2}-\\dfrac{x^{2}\\ln x}{2}+\\dfrac{x^{2}}{4}$']
});
add('medium', '순환 부분적분', 'e^x*cos(x)', 'e^x*(sin(x)+cos(x))/2', {
  domain: [0.2, 2.4],
  hints: ['부분적분을 두 번 하면 원래 적분이 돌아온다.', '$I=e^{x}(\\sin x+\\cos x)-I$'],
  steps: ['두 번 부분적분', '$I=\\dfrac{e^{x}(\\sin x+\\cos x)}{2}$']
});
add('medium', '순환 부분적분', 'e^(-x)*sin(2*x)', 'e^(-x)*(-sin(2*x)-2*cos(2*x))/5', {
  domain: [0.2, 1.4],
  hints: ['$\\int e^{ax}\\sin bx\\,dx=\\dfrac{e^{ax}(a\\sin bx-b\\cos bx)}{a^{2}+b^{2}}$',
          '$a=-1,\;b=2$ 이므로 분모는 $5$ 다.'],
  steps: ['공식에 $a=-1,\;b=2$ 를 대입', '$=\\dfrac{e^{-x}(-\\sin 2x-2\\cos 2x)}{5}$']
});
add('medium', '부분적분', 'x^2*sin(x)', '-x^2*cos(x)+2*x*sin(x)+2*cos(x)', {
  domain: D.trigW,
  hints: ['부분적분을 두 번 한다.', '$\\int x\\cos x\\,dx=x\\sin x+\\cos x$'],
  steps: ['$=-x^{2}\\cos x+2\\int x\\cos x\\,dx$', '$=-x^{2}\\cos x+2x\\sin x+2\\cos x$']
});
add('medium', '부분적분', 'x^2*cos(x)', 'x^2*sin(x)+2*x*cos(x)-2*sin(x)', {
  domain: D.trigW,
  hints: ['부분적분을 두 번 한다.', '$\\int x\\sin x\\,dx=-x\\cos x+\\sin x$'],
  steps: ['$=x^{2}\\sin x-2\\int x\\sin x\\,dx$', '$=x^{2}\\sin x+2x\\cos x-2\\sin x$']
});
add('medium', '부분적분', 'arccos(x)', 'x*arccos(x)-sqrt(1-x^2)', {
  domain: D.unit,
  hints: ['$dv=dx$ 로 부분적분한다.', '$(\\arccos x)\'=-\\dfrac{1}{\\sqrt{1-x^{2}}}$'],
  steps: ['$=x\\arccos x+\\int\\dfrac{x}{\\sqrt{1-x^{2}}}dx$', '$=x\\arccos x-\\sqrt{1-x^{2}}$']
});
add('hard', '치환 후 부분적분', 'sin(sqrt(x))', '2*sin(sqrt(x))-2*sqrt(x)*cos(sqrt(x))', {
  domain: [0.3, 3.0],
  hints: ['$u=\\sqrt x$ 로 두면 $2\\int u\\sin u\\,du$ 다.', '$\\int u\\sin u\\,du=\\sin u-u\\cos u$'],
  steps: ['$u=\\sqrt x,\;dx=2u\\,du$', '$2(\\sin u-u\\cos u)$']
});
add('hard', '치환 후 부분적분', 'cos(sqrt(x))', '2*cos(sqrt(x))+2*sqrt(x)*sin(sqrt(x))', {
  domain: [0.3, 3.0],
  hints: ['$u=\\sqrt x$ 로 두면 $2\\int u\\cos u\\,du$ 다.', '$\\int u\\cos u\\,du=\\cos u+u\\sin u$'],
  steps: ['$u=\\sqrt x$', '$2(\\cos u+u\\sin u)$']
});
add('medium', '삼각 곱의 합 변환', 'sin(x)*cos(3*x)', '-cos(4*x)/8+cos(2*x)/4', {
  domain: D.trigW,
  hints: ['곱을 합으로: $\\sin A\\cos B=\\dfrac{\\sin(A+B)+\\sin(A-B)}{2}$', '$\\sin 4x$ 와 $-\\sin 2x$ 로 갈라진다.'],
  steps: ['$\\sin x\\cos 3x=\\dfrac{\\sin 4x-\\sin 2x}{2}$', '$=-\\dfrac{\\cos 4x}{8}+\\dfrac{\\cos 2x}{4}$']
});
add('medium', '삼각 곱의 합 변환', 'sin(3*x)*sin(5*x)', 'sin(2*x)/4-sin(8*x)/16', {
  domain: D.trigW,
  hints: ['$\\sin A\\sin B=\\dfrac{\\cos(A-B)-\\cos(A+B)}{2}$', '$\\cos 2x$ 와 $\\cos 8x$ 로 갈라진다.'],
  steps: ['$\\sin 3x\\sin 5x=\\dfrac{\\cos 2x-\\cos 8x}{2}$', '$=\\dfrac{\\sin 2x}{4}-\\dfrac{\\sin 8x}{16}$']
});
add('hard', '삼각함수 고차', 'tan(x)^4', 'tan(x)^3/3-tan(x)+x', {
  domain: D.trig,
  hints: ['$\\tan^{4}=\\tan^{2}(\\sec^{2}-1)$ 로 한 단계 내린다.', '$\\int\\tan^{2}x\\,dx=\\tan x-x$'],
  steps: ['$\\int\\tan^{4}=\\dfrac{\\tan^{3}}{3}-\\int\\tan^{2}$', '$=\\dfrac{\\tan^{3}x}{3}-\\tan x+x$']
});
add('hard', '삼각함수 고차', 'sec(x)*tan(x)^3', 'sec(x)^3/3-sec(x)', {
  domain: D.trig,
  hints: ['$\\sec x\\tan^{3}x=(\\sec^{2}x-1)\\sec x\\tan x$ 로 정리한다.', '$u=\\sec x$ 로 둔다.'],
  steps: ['$u=\\sec x,\;du=\\sec x\\tan x\\,dx$', '$\\int(u^{2}-1)du=\\dfrac{\\sec^{3}x}{3}-\\sec x$']
});
add('hard', '삼각함수 고차', 'cot(x)^3', '-cot(x)^2/2-ln(sin(x))', {
  domain: D.trig, lnAbs: true,
  hints: ['$\\cot^{3}=\\cot(\\csc^{2}-1)$ 로 쪼갠다.', '$\\int\\cot x\\,dx=\\ln|\\sin x|$'],
  steps: ['$\\int\\cot^{3}=-\\dfrac{\\cot^{2}}{2}-\\int\\cot x\\,dx$', '$=-\\dfrac{\\cot^{2}x}{2}-\\ln|\\sin x|$']
});
add('hard', '삼각함수 고차', 'csc(x)^4', '-cot(x)-cot(x)^3/3', {
  domain: [0.35, 1.3],
  hints: ['$\\csc^{4}=\\csc^{2}(1+\\cot^{2})$ 로 쓴다.', '$u=\\cot x,\;du=-\\csc^{2}x\\,dx$'],
  steps: ['$u=\\cot x$', '$-\\int(1+u^{2})du=-\\cot x-\\dfrac{\\cot^{3}x}{3}$']
});
add('hard', '삼각함수 홀수차', 'sin(x)^2*cos(x)^3', 'sin(x)^3/3-sin(x)^5/5', {
  domain: D.trigW,
  hints: ['$\\cos^{3}=\\cos(1-\\sin^{2})$ 로 하나를 떼어낸다.', '$u=\\sin x$ 로 치환한다.'],
  steps: ['$u=\\sin x$', '$\\int(u^{2}-u^{4})du=\\dfrac{\\sin^{3}x}{3}-\\dfrac{\\sin^{5}x}{5}$']
});
add('hard', '삼각함수 홀수차', 'sin(x)^3*cos(x)^3', 'sin(x)^4/4-sin(x)^6/6', {
  domain: D.trigW,
  hints: ['$\\cos^{3}=\\cos(1-\\sin^{2})$ 로 떼어낸다.', '$u=\\sin x$ 치환.'],
  steps: ['$u=\\sin x$', '$\\int(u^{3}-u^{5})du=\\dfrac{\\sin^{4}x}{4}-\\dfrac{\\sin^{6}x}{6}$']
});
add('medium', '부분분수', 'x/((x+1)*(x+2))', '-ln(x+1)+2*ln(x+2)', {
  domain: [0.3, 2.6],
  hints: ['가리기(cover-up)로 $x=-1,\,-2$ 를 대입한다.', '계수는 $-1$ 과 $2$ 다.'],
  steps: ['$\\dfrac{x}{(x+1)(x+2)}=-\\dfrac{1}{x+1}+\\dfrac{2}{x+2}$', '각 항을 로그로 적분']
});
add('medium', '부분분수', '(x^2+1)/(x*(x^2-1))', 'ln(x^2-1)-ln(x)', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['$\\dfrac{x^{2}+1}{x(x-1)(x+1)}$ 로 보고 가리기를 쓴다.', '계수는 $-1,\,1,\,1$ 이다.'],
  steps: ['$=-\\dfrac1x+\\dfrac{1}{x-1}+\\dfrac{1}{x+1}$', '$=\\ln\\left|\\dfrac{x^{2}-1}{x}\\right|$']
});
add('hard', '부분분수', '1/(x^2*(x+1))', '-1/x-ln(x)+ln(x+1)', {
  domain: D.pos,
  hints: ['$\\dfrac{1}{x^{2}(x+1)}=\\dfrac{A}{x}+\\dfrac{B}{x^{2}}+\\dfrac{C}{x+1}$ 로 놓는다.', '$B=1,\;C=1,\;A=-1$'],
  steps: ['$=-\\dfrac1x+\\dfrac{1}{x^{2}}+\\dfrac{1}{x+1}$', '$=-\\dfrac1x+\\ln\\left|\\dfrac{x+1}{x}\\right|$']
});
add('hard', '완전제곱', '(3*x+2)/(x^2+4*x+8)', '3*ln(x^2+4*x+8)/2-2*arctan((x+2)/2)', {
  domain: [0.2, 2.8],
  hints: ['분자를 $\\dfrac32(2x+4)-4$ 로 쪼갠다.', '$x^{2}+4x+8=(x+2)^{2}+4$'],
  steps: ['$\\dfrac32\\int\\dfrac{2x+4}{x^{2}+4x+8}dx=\\dfrac32\\ln(x^{2}+4x+8)$',
          '$-4\\int\\dfrac{dx}{(x+2)^{2}+4}=-2\\arctan\\dfrac{x+2}{2}$']
});
add('hard', '삼각 치환', 'sqrt(x^2-1)', 'x*sqrt(x^2-1)/2-acosh(x)/2', {
  domain: D.gt1,
  hints: ['$x=\\cosh t$ 로 두면 $\\int\\sinh^{2}t\\,dt$ 가 된다.', '$\\sinh^{2}t=\\dfrac{\\cosh 2t-1}{2}$'],
  steps: ['$x=\\cosh t$', '$\\int\\sinh^{2}t\\,dt=\\dfrac{\\sinh 2t}{4}-\\dfrac t2$',
          '$=\\dfrac{x\\sqrt{x^{2}-1}}{2}-\\dfrac{\\operatorname{arcosh}x}{2}$']
});
add('hard', '삼각 치환', 'sqrt(4-x^2)', 'x*sqrt(4-x^2)/2+2*arcsin(x/2)', {
  domain: [-1.4, 1.5],
  hints: ['$x=2\\sin\\theta$ 로 두면 $4\\int\\cos^{2}\\theta\\,d\\theta$ 다.', '반각공식으로 내린다.'],
  steps: ['$x=2\\sin\\theta$', '$4\\int\\cos^{2}\\theta\\,d\\theta=2\\theta+\\sin 2\\theta$',
          '$=2\\arcsin\\dfrac x2+\\dfrac{x\\sqrt{4-x^{2}}}{2}$']
});
add('hard', '삼각 치환', '1/(x^2*sqrt(4-x^2))', '-sqrt(4-x^2)/(4*x)', {
  domain: [0.5, 1.7],
  hints: ['$x=2\\sin\\theta$ 로 두면 $\\dfrac14\\int\\csc^{2}\\theta\\,d\\theta$ 다.', '$\\cot\\theta=\\dfrac{\\sqrt{4-x^{2}}}{x}$'],
  steps: ['$x=2\\sin\\theta$', '$-\\dfrac{\\cot\\theta}{4}=-\\dfrac{\\sqrt{4-x^{2}}}{4x}$']
});
add('medium', '치환적분', 'x*sqrt(x-1)', '2*(x-1)^(5/2)/5+2*(x-1)^(3/2)/3', {
  domain: [1.3, 3.4],
  hints: ['$u=x-1$ 로 두고 $x=u+1$ 을 대입한다.', '$\\int(u^{3/2}+u^{1/2})du$'],
  steps: ['$u=x-1$', '$\\int(u+1)\\sqrt u\\,du=\\dfrac{2u^{5/2}}{5}+\\dfrac{2u^{3/2}}{3}$']
});
add('medium', '치환적분', 'x/sqrt(x+1)', '2*(x+1)^(3/2)/3-2*sqrt(x+1)', {
  domain: [0.2, 3.0],
  hints: ['$u=x+1$ 로 두고 $x=u-1$ 을 대입한다.', '$\\int\\left(\\sqrt u-\\dfrac{1}{\\sqrt u}\\right)du$'],
  steps: ['$u=x+1$', '$\\dfrac{2u^{3/2}}{3}-2u^{1/2}$']
});
add('medium', '치환적분', '1/(sqrt(x)+1)', '2*sqrt(x)-2*ln(sqrt(x)+1)', {
  domain: D.pos,
  hints: ['$u=\\sqrt x$ 로 두면 $\\int\\dfrac{2u}{u+1}du$ 다.', '$\\dfrac{u}{u+1}=1-\\dfrac{1}{u+1}$'],
  steps: ['$u=\\sqrt x,\;dx=2u\\,du$', '$2\\int\\left(1-\\dfrac{1}{u+1}\\right)du=2\\sqrt x-2\\ln(\\sqrt x+1)$']
});
add('medium', '치환적분', '1/(sqrt(x)*(1+sqrt(x))^2)', '-2/(1+sqrt(x))', {
  domain: D.pos,
  hints: ['$u=\\sqrt x$ 로 두면 $\\int\\dfrac{2\\,du}{(1+u)^{2}}$ 다.', '$\\int(1+u)^{-2}du=-\\dfrac{1}{1+u}$'],
  steps: ['$u=\\sqrt x$', '$-\\dfrac{2}{1+\\sqrt x}$']
});
add('medium', '치환적분', '1/(x*ln(x)^2)', '-1/ln(x)', {
  domain: [1.4, 4.2],
  hints: ['$u=\\ln x$ 로 두면 $\\int u^{-2}du$ 다.', '$\\int u^{-2}du=-\\dfrac1u$'],
  steps: ['$u=\\ln x$', '$-\\dfrac{1}{\\ln x}$']
});
add('hard', '지수 부분분수', 'e^x/(e^(2*x)+3*e^x+2)', 'ln(e^x+1)-ln(e^x+2)', {
  domain: [-1.2, 1.6],
  hints: ['$u=e^{x}$ 로 두면 $\\int\\dfrac{du}{(u+1)(u+2)}$ 다.',
          '$\\dfrac{1}{(u+1)(u+2)}=\\dfrac{1}{u+1}-\\dfrac{1}{u+2}$'],
  steps: ['$u=e^{x}$', '$\\ln\\dfrac{u+1}{u+2}=\\ln\\dfrac{e^{x}+1}{e^{x}+2}$']
});
add('hard', '쌍곡선함수', 'sinh(x)^2', 'sinh(2*x)/4-x/2', {
  domain: D.hypP,
  hints: ['$\\sinh^{2}x=\\dfrac{\\cosh 2x-1}{2}$ 를 쓴다.', '$\\int\\cosh 2x\\,dx=\\dfrac{\\sinh 2x}{2}$'],
  steps: ['$\\sinh^{2}x=\\dfrac{\\cosh 2x-1}{2}$', '$=\\dfrac{\\sinh 2x}{4}-\\dfrac x2$']
});
add('hard', '쌍곡선함수', 'x*sinh(x)', 'x*cosh(x)-sinh(x)', {
  domain: D.hypP,
  hints: ['$dv=\\sinh x\\,dx\\Rightarrow v=\\cosh x$', '$\\int\\cosh x\\,dx=\\sinh x$'],
  steps: ['$=x\\cosh x-\\int\\cosh x\\,dx$', '$=x\\cosh x-\\sinh x$']
});
add('hard', '치환적분', 'sec(x)^4/sqrt(tan(x))', '2*sqrt(tan(x))+2*tan(x)^(5/2)/5', {
  domain: [0.3, 1.2],
  hints: ['$\\sec^{4}=\\sec^{2}(1+\\tan^{2})$ 로 쪼갠다.', '$u=\\tan x,\;du=\\sec^{2}x\\,dx$'],
  steps: ['$u=\\tan x$', '$\\int\\dfrac{1+u^{2}}{\\sqrt u}du=2\\sqrt u+\\dfrac{2u^{5/2}}{5}$']
});

add('monster', '몫의 미분 되짚기', '(x^2+20)/(x*sin(x)+5*cos(x))^2',
    '(5*sin(x)-x*cos(x))/(x*sin(x)+5*cos(x))', {
  domain: [0.25, 1.3],
  hints: ['분모의 미분 $(x\\sin x+5\\cos x)\'=x\\cos x-4\\sin x$ 를 먼저 계산해 둔다.',
          '$\\dfrac{5\\sin x-x\\cos x}{x\\sin x+5\\cos x}$ 를 미분해 보면 그대로 나온다.'],
  steps: ['$N=5\\sin x-x\\cos x,\;D=x\\sin x+5\\cos x$ 로 두고 $\\left(\\dfrac ND\\right)\'$ 를 계산한다',
          '$N\'D-ND\'=x^{2}+20$', '따라서 원시함수는 $\\dfrac ND$']
});
add('monster', '삼각 치환', '1/((1+x^2)*sqrt(1-x^2))', 'arctan(sqrt(2)*x/sqrt(1-x^2))/sqrt(2)', {
  domain: D.unit,
  hints: ['$x=\\sin\\theta$ 로 두면 $\\int\\dfrac{d\\theta}{1+\\sin^{2}\\theta}$ 다.',
          '분자·분모를 $\\cos^{2}\\theta$ 로 나눠 $u=\\tan\\theta$ 로 둔다.'],
  steps: ['$x=\\sin\\theta$', '$\\int\\dfrac{\\sec^{2}\\theta\\,d\\theta}{1+2\\tan^{2}\\theta}=\\dfrac{1}{\\sqrt2}\\arctan(\\sqrt2\\tan\\theta)$',
          '$\\tan\\theta=\\dfrac{x}{\\sqrt{1-x^{2}}}$']
});
add('monster', '삼각 치환', '1/((1-x^2)*sqrt(1+x^2))', 'atanh(sqrt(2)*x/sqrt(1+x^2))/sqrt(2)', {
  domain: [-0.8, 0.8],
  hints: ['$x=\\sinh t$ 로 두면 $\\int\\dfrac{dt}{1-\\sinh^{2}t}$ 다.',
          '$g=\\dfrac{x}{\\sqrt{1+x^{2}}}$ 로 두면 $g\'=(1+x^{2})^{-3/2}$ 다.'],
  steps: ['$g=\\dfrac{x}{\\sqrt{1+x^{2}}}$',
          '$\\dfrac{d}{dx}\\operatorname{artanh}(\\sqrt2 g)=\\dfrac{\\sqrt2}{(1-x^{2})\\sqrt{1+x^{2}}}$',
          '$\\dfrac{1}{\\sqrt2}$ 를 곱해 맞춘다']
});
add('monster', '역수 치환', '(x^2+1)/(x*sqrt(x^4+3*x^2+1))', 'asinh((x^2-1)/(sqrt(5)*x))', {
  domain: [0.35, 2.6],
  hints: ['분자·분모를 $x^{2}$ 로 나누면 $\\dfrac{1+x^{-2}}{\\sqrt{x^{2}+3+x^{-2}}}$ 다.',
          '$u=x-\\dfrac1x$ 로 두면 근호 안이 $u^{2}+5$ 다.'],
  steps: ['$u=x-\\dfrac1x,\;x^{2}+x^{-2}=u^{2}+2$',
          '$\\int\\dfrac{du}{\\sqrt{u^{2}+5}}=\\operatorname{arsinh}\\dfrac{u}{\\sqrt5}$']
});
add('monster', '역수 치환', '(x^2-1)/(x*sqrt(x^4+x^2+1))', 'acosh((x^2+1)/x)', {
  domain: [0.35, 2.6],
  hints: ['분자·분모를 $x^{2}$ 로 나눈다.', '$u=x+\\dfrac1x$ 로 두면 근호 안이 $u^{2}-1$ 이다.'],
  steps: ['$u=x+\\dfrac1x,\;x^{2}+1+x^{-2}=u^{2}-1$',
          '$\\int\\dfrac{du}{\\sqrt{u^{2}-1}}=\\operatorname{arcosh}\\left(x+\\dfrac1x\\right)$']
});
add('monster', '삼각 유리식', '1/(sin(x)^3*cos(x))', 'ln(tan(x))-1/(2*sin(x)^2)', {
  domain: [0.35, 1.2], lnAbs: true,
  hints: ['분자에 $\\sin^{2}x+\\cos^{2}x=1$ 을 끼워 넣는다.',
          '$\\dfrac{1}{\\sin^{3}x\\cos x}=\\dfrac{1}{\\sin x\\cos x}+\\dfrac{\\cos x}{\\sin^{3}x}$'],
  steps: ['$\\int\\dfrac{dx}{\\sin x\\cos x}=\\ln|\\tan x|$',
          '$\\int\\dfrac{\\cos x}{\\sin^{3}x}dx=-\\dfrac{1}{2\\sin^{2}x}$']
});
add('monster', '반각 치환', '1/(3+5*cos(x))', 'ln((2+tan(x/2))/(2-tan(x/2)))/4', {
  domain: [0.3, 2.0], lnAbs: true,
  hints: ['$t=\\tan\\dfrac x2$ 치환에서 $\\cos x=\\dfrac{1-t^{2}}{1+t^{2}},\;dx=\\dfrac{2dt}{1+t^{2}}$',
          '정리하면 $\\int\\dfrac{dt}{4-t^{2}}$ 가 된다.'],
  steps: ['$t=\\tan\\dfrac x2$', '$\\int\\dfrac{2dt}{8-2t^{2}}=\\int\\dfrac{dt}{4-t^{2}}$',
          '$=\\dfrac14\\ln\\left|\\dfrac{2+t}{2-t}\\right|$']
});

// ================================================================== 몬스터 추가분 3
// MIT Integration Bee (2023~2026) 준결승·결승·타이브레이커 부정적분 문제들.
// 출처: https://math.mit.edu/~yyao1/integrationbee.html

add('monster', '위장된 미분', 'x^2/sqrt(4*e^(2*x)+(x^2+2*x+2)^2)', '-asinh((x^2+2*x+2)/(2*e^x))', {
  domain: [0.2, 2.4],
  hints: ['$g=\\dfrac{x^{2}+2x+2}{2e^{x}}$ 로 두고 $g\'$ 를 계산해 본다.',
          '$g\'=-\\dfrac{x^{2}}{2e^{x}}$ 이고, 근호 안은 정확히 $4e^{2x}(1+g^{2})$ 다.'],
  steps: ['$g=\\dfrac{x^{2}+2x+2}{2e^{x}},\;g\'=-\\dfrac{x^{2}}{2e^{x}}$',
          '$\\sqrt{4e^{2x}+(x^{2}+2x+2)^{2}}=2e^{x}\\sqrt{1+g^{2}}$',
          '$-\\dfrac{d}{dx}\\operatorname{arsinh}g=-\\dfrac{g\'}{\\sqrt{1+g^{2}}}=$ 피적분함수']
});
add('monster', '삼각 곱 항등식', '1/(cos(x)*cos(x+2*pi/3)*cos(x-2*pi/3))^2', '16*tan(3*x)/3', {
  domain: [0.05, 0.48],
  hints: ['$\\cos\\theta\\cos\\left(\\theta+\\dfrac{2\\pi}{3}\\right)\\cos\\left(\\theta-\\dfrac{2\\pi}{3}\\right)=\\dfrac{\\cos 3\\theta}{4}$',
          '정리하면 $16\\sec^{2}3x$ 만 남는다.'],
  steps: ['세 코사인의 곱은 $\\dfrac{\\cos 3x}{4}$',
          '$\\int\\dfrac{16}{\\cos^{2}3x}dx=\\dfrac{16\\tan 3x}{3}$']
});
add('monster', '미분 꼴 알아보기', '(x+1)*e^x*ln(x)', 'e^x*(x*ln(x)-1)', {
  domain: D.pos,
  hints: ['$\\int e^{x}(f+f\')dx=e^{x}f$ 를 노리고 $f=x\\ln x-1$ 을 시험한다.',
          '$f\'=\\ln x+1$ 이므로 $f+f\'=x\\ln x+\\ln x=(x+1)\\ln x$'],
  steps: ['$f=x\\ln x-1,\;f\'=\\ln x+1$', '$f+f\'=(x+1)\\ln x$', '$=e^{x}(x\\ln x-1)$']
});
add('monster', '세제곱근 인수분해', 'x/(x^3-3*x-2)^(1/3)', '((x+1)*(x-2)^2)^(1/3)', {
  domain: [2.3, 4.5],
  hints: ['$x^{3}-3x-2=(x+1)^{2}(x-2)$ 로 인수분해된다.',
          '$F=\\sqrt[3]{(x+1)(x-2)^{2}}$ 를 세제곱해서 음함수 미분해 본다.'],
  steps: ['$F^{3}=(x+1)(x-2)^{2}$', '$3F^{2}F\'=3x(x-2)$',
          '$F\'=\\dfrac{x(x-2)}{(x+1)^{2/3}(x-2)^{4/3}}=\\dfrac{x}{\\sqrt[3]{(x+1)^{2}(x-2)}}$']
});
add('monster', '고차 부분분수', '1/(x^8-x^6)', 'ln((x-1)/(x+1))/2+1/x+1/(3*x^3)+1/(5*x^5)', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['$t=x^{2}$ 로 보면 $\\dfrac{1}{t^{3}(t-1)}=\\dfrac{1}{t-1}-\\dfrac1t-\\dfrac{1}{t^{2}}-\\dfrac{1}{t^{3}}$ 다.',
          '되돌리면 $\\dfrac{1}{x^{2}-1}-\\dfrac{1}{x^{2}}-\\dfrac{1}{x^{4}}-\\dfrac{1}{x^{6}}$'],
  steps: ['$\\dfrac{1}{x^{6}(x^{2}-1)}=\\dfrac{1}{x^{2}-1}-\\dfrac{1}{x^{2}}-\\dfrac{1}{x^{4}}-\\dfrac{1}{x^{6}}$',
          '$=\\dfrac12\\ln\\left|\\dfrac{x-1}{x+1}\\right|+\\dfrac1x+\\dfrac{1}{3x^{3}}+\\dfrac{1}{5x^{5}}$']
});
add('monster', '역수 치환', '(3*x^2+7*x-5)*(x+1/x)*e^(x+1/x)', '(3*x^3-2*x^2+5*x)*e^(x+1/x)', {
  domain: [0.5, 2.0],
  hints: ['답을 $P(x)e^{x+1/x}$ 꼴로 놓고 $P$ 를 미정계수로 찾는다.',
          '$\\left(Pe^{u}\\right)\'=\\left(P\'+P\\left(1-\\dfrac{1}{x^{2}}\\right)\\right)e^{u}$'],
  steps: ['$P=3x^{3}-2x^{2}+5x$ 로 두면',
          '$P\'+P\\left(1-\\dfrac{1}{x^{2}}\\right)=3x^{3}+7x^{2}-2x+7-\\dfrac5x$',
          '이는 $(3x^{2}+7x-5)\\left(x+\\dfrac1x\\right)$ 와 같다']
});
add('monster', '부분분수', '(x+24)/(x^3+25*x^2+144*x)', 'ln(x)/6-5*ln(x+9)/21+ln(x+16)/14', {
  domain: D.pos, lnAbs: true,
  hints: ['$x^{3}+25x^{2}+144x=x(x+9)(x+16)$ 로 인수분해된다.',
          '가리기(cover-up)로 $x=0,\\,-9,\\,-16$ 을 차례로 대입한다.'],
  steps: ['$\\dfrac{x+24}{x(x+9)(x+16)}=\\dfrac{1/6}{x}-\\dfrac{5/21}{x+9}+\\dfrac{1/14}{x+16}$',
          '각 항을 로그로 적분한다']
});
add('monster', '역수 치환', 'sqrt((x^6+1)*(x^2+1))/x^3',
    '((1-1/x^2)*sqrt(x^4-x^2+1)+asinh((x^2-1)/x))/2', {
  domain: [0.4, 2.6],
  hints: ['$(x^{6}+1)(x^{2}+1)=(x^{2}+1)^{2}(x^{4}-x^{2}+1)$ 로 묶인다.',
          '$u=x-\\dfrac1x$ 로 두면 $x^{4}-x^{2}+1=x^{2}(u^{2}+1)$ 이고 $du=\\left(1+\\dfrac{1}{x^{2}}\\right)dx$ 다.'],
  steps: ['피적분함수 $=\\left(1+\\dfrac{1}{x^{2}}\\right)\\sqrt{u^{2}+1}$',
          '$\\int\\sqrt{u^{2}+1}\\,du=\\dfrac{u\\sqrt{u^{2}+1}+\\operatorname{arsinh}u}{2}$']
});
add('monster', '위장된 치환', '(arctan(x)-x*arctan(x))/(1-x+x^2-x^3)', 'arctan(x)^2/2', {
  domain: [0.15, 0.9],
  hints: ['분모를 $(1-x)(1+x^{2})$ 로 인수분해한다.', '분자는 $(1-x)\\arctan x$ 이므로 통째로 약분된다.'],
  steps: ['$\\dfrac{(1-x)\\arctan x}{(1-x)(1+x^{2})}=\\dfrac{\\arctan x}{1+x^{2}}$',
          '$u=\\arctan x:\;\\dfrac{\\arctan^{2}x}{2}$']
});
add('monster', '적분대회 결승', 'e^(x/2)*cos(x)/(3*cos(x)+4*sin(x))^(1/3)',
    '6*(3*cos(x)+4*sin(x))^(2/3)*e^(x/2)/25', {
  domain: [0.2, 2.0],
  hints: ['답을 $c\\,(3\\cos x+4\\sin x)^{2/3}e^{x/2}$ 로 놓고 미분해 계수를 맞춘다.',
          '$\\sin$ 항이 저절로 사라지고 $\\cos$ 항만 남는 것이 핵심이다.'],
  steps: ['$F=c(3\\cos x+4\\sin x)^{2/3}e^{x/2}$',
          '$F\'=c\\,e^{x/2}(3\\cos x+4\\sin x)^{-1/3}\\left[\\dfrac23(4\\cos x-3\\sin x)+\\dfrac12(3\\cos x+4\\sin x)\\right]$',
          '대괄호 $=\\dfrac{25}{6}\\cos x$ 이므로 $c=\\dfrac{6}{25}$']
});
add('monster', '적분대회 결승', '1/(x^4+1)^(1/4)',
    'arctan(x/(1+x^4)^(1/4))/2+ln(((1+x^4)^(1/4)+x)/((1+x^4)^(1/4)-x))/4', {
  domain: [0.3, 2.6], lnAbs: true,
  hints: ['$t=\\dfrac{x}{\\sqrt[4]{1+x^{4}}}$ 로 두면 $dt=\\dfrac{dx}{(1+x^{4})^{5/4}}$ 이고 $1-t^{4}=\\dfrac{1}{1+x^{4}}$ 다.',
          '$\\int\\dfrac{dt}{1-t^{4}}$ 로 바뀐다.'],
  steps: ['$t=\\dfrac{x}{\\sqrt[4]{1+x^{4}}}$ 치환',
          '$\\int\\dfrac{dt}{1-t^{4}}=\\dfrac{\\arctan t}{2}+\\dfrac14\\ln\\left|\\dfrac{1+t}{1-t}\\right|$',
          '$t$ 를 되돌린다']
});
add('monster', '숨은 완전제곱', 'sqrt(x^4-4*x+3)',
    '(x^2+2*x+3)^(3/2)/3-(x+1)*sqrt(x^2+2*x+3)-2*ln(sqrt(x^2+2*x+3)+x+1)', {
  domain: [1.3, 3.4],
  hints: ['$x^{4}-4x+3=(x-1)^{2}(x^{2}+2x+3)$ 으로 인수분해된다.',
          '$x>1$ 에서는 $\\sqrt{x^{4}-4x+3}=(x-1)\\sqrt{x^{2}+2x+3}$ 다.'],
  steps: ['$(x-1)\\sqrt{x^{2}+2x+3}=\\left((x+1)-2\\right)\\sqrt{u}$, $u=x^{2}+2x+3$',
          '$\\int(x+1)\\sqrt u\\,dx=\\dfrac{u^{3/2}}{3}$',
          '$\\int\\dfrac{2u\\,dx}{\\sqrt u}$ 를 $\\sqrt{(x+1)^{2}+2}$ 로 보고 정리한다']
});
add('monster', '이항 전개', '(x/(x-1))^4', 'x+4*ln(x-1)-6/(x-1)-2/(x-1)^2-1/(3*(x-1)^3)', {
  domain: [1.6, 4.0], lnAbs: true,
  hints: ['$\\dfrac{x}{x-1}=1+\\dfrac{1}{x-1}$ 로 쓰고 네제곱을 이항전개한다.',
          '$1+\\dfrac{4}{x-1}+\\dfrac{6}{(x-1)^{2}}+\\dfrac{4}{(x-1)^{3}}+\\dfrac{1}{(x-1)^{4}}$'],
  steps: ['이항전개 후 항별로 적분한다',
          '$=x+4\\ln|x-1|-\\dfrac{6}{x-1}-\\dfrac{2}{(x-1)^{2}}-\\dfrac{1}{3(x-1)^{3}}$']
});
add('monster', '탄젠트 덧셈정리', '(tan(3*x)+tan(4*x))*cos(3*x)*cos(4*x)/cos(7*x)', '-ln(cos(7*x))/7', {
  domain: [0.02, 0.2], lnAbs: true,
  hints: ['분자를 통분하면 $\\sin 3x\\cos 4x+\\cos 3x\\sin 4x$ 다.',
          '덧셈정리로 $\\sin 7x$ 가 되어 $\\tan 7x$ 만 남는다.'],
  steps: ['$(\\tan 3x+\\tan 4x)\\cos 3x\\cos 4x=\\sin(3x+4x)=\\sin 7x$',
          '$\\int\\tan 7x\\,dx=-\\dfrac{\\ln|\\cos 7x|}{7}$']
});
add('monster', '지수탑 미분', 'ln(x)*((x/e)^x+(e/x)^x)', '(x/e)^x-(e/x)^x', {
  domain: [0.4, 2.6],
  hints: ['$\\left(\\dfrac xe\\right)^{x}=e^{x(\\ln x-1)}$, $\\left(\\dfrac ex\\right)^{x}=e^{x(1-\\ln x)}$ 로 쓴다.',
          '두 함수의 도함수가 각각 $+\\ln x$ 배, $-\\ln x$ 배다.'],
  steps: ['$\\dfrac{d}{dx}\\left(\\dfrac xe\\right)^{x}=\\left(\\dfrac xe\\right)^{x}\\ln x$',
          '$\\dfrac{d}{dx}\\left(\\dfrac ex\\right)^{x}=-\\left(\\dfrac ex\\right)^{x}\\ln x$',
          '차를 취하면 합이 나온다']
});
add('monster', '삼각 곱의 합 변환',
    'cos(3*x)*cos(5*x)*cos(6*x)*cos(7*x)-cos(x)*cos(2*x)*cos(4*x)*cos(8*x)',
    'sin(21*x)/168-sin(13*x)/104', {
  domain: [0.2, 1.2],
  hints: ['네 코사인의 곱을 두 번씩 묶어 합으로 바꾸면 각각 8개 항이 된다.',
          '두 전개는 $\\cos 21x$ 와 $\\cos 13x$ 만 빼고 전부 같다.'],
  steps: ['첫 곱 $=\\dfrac18(\\cos 21x+\\cos 15x+\\cos 11x+\\cos 9x+\\cos 7x+\\cos 5x+\\cos 3x+\\cos x)$',
          '둘째 곱은 $\\cos 21x$ 자리에 $\\cos 13x$ 가 온다',
          '차 $=\\dfrac{\\cos 21x-\\cos 13x}{8}$']
});
add('monster', '분수 지수', '(1-2*x)/((1+x)^2*x^(2/3))', '3*x^(1/3)/(1+x)', {
  domain: D.pos,
  hints: ['답을 $\\dfrac{3x^{1/3}}{1+x}$ 로 놓고 몫의 미분법을 확인해 본다.',
          '$x^{-2/3}\\left[(1+x)-3x\\right]=(1-2x)x^{-2/3}$'],
  steps: ['$\\left(\\dfrac{3x^{1/3}}{1+x}\\right)\'=\\dfrac{x^{-2/3}(1+x)-3x^{1/3}}{(1+x)^{2}}$',
          '$=\\dfrac{1-2x}{(1+x)^{2}x^{2/3}}$']
});
add('monster', '위장된 미분', 'e^(cos(x))*cos(2*x+sin(x))', 'e^(cos(x))*(sin(x+sin(x))-sin(sin(x)))', {
  domain: D.trigW,
  hints: ['$2x+\\sin x=(x+\\sin x)+x$ 로 쪼개 덧셈정리를 쓴다.',
          '$\\left(e^{\\cos x}\\sin(x+\\sin x)\\right)\'$ 와 $\\left(e^{\\cos x}\\sin(\\sin x)\\right)\'$ 를 비교한다.'],
  steps: ['$\\left(e^{\\cos x}\\sin(x+\\sin x)\\right)\'=e^{\\cos x}\\left[(1+\\cos x)\\cos(x+\\sin x)-\\sin x\\sin(x+\\sin x)\\right]$',
          '$\\left(e^{\\cos x}\\sin(\\sin x)\\right)\'=e^{\\cos x}\\left[\\cos x\\cos(\\sin x)-\\sin x\\sin(\\sin x)\\right]$',
          '두 식을 빼면 $e^{\\cos x}\\cos(2x+\\sin x)$ 가 남는다']
});
add('monster', '로그 치환', '(3*ln(x)-1+2*x)/(x*ln(x)+x^2+2*x^4)', '3*ln(x)-ln(ln(x)+x+2*x^3)', {
  domain: [1.2, 3.0], lnAbs: true,
  hints: ['분모를 $x\\left(\\ln x+x+2x^{3}\\right)$ 로 묶는다.',
          '$w=\\ln x+x+2x^{3}$ 라 하면 $\\dfrac3x-\\dfrac{w\'}{w}$ 가 피적분함수와 같은지 확인한다.'],
  steps: ['$w=\\ln x+x+2x^{3},\;w\'=\\dfrac1x+1+6x^{2}$',
          '$\\dfrac3x-\\dfrac{w\'}{w}=\\dfrac{3w-xw\'}{xw}=\\dfrac{3\\ln x+2x-1}{xw}$',
          '$=3\\ln x-\\ln|w|$']
});
add('monster', '무리 지수', '(sqrt(x+1)-sqrt(x))^pi',
    '((sqrt(x+1)-sqrt(x))^(pi+2)/(pi+2)-(sqrt(x+1)-sqrt(x))^(pi-2)/(pi-2))/2', {
  domain: [0.3, 3.0],
  hints: ['$t=\\sqrt{x+1}-\\sqrt x$ 로 두면 $\\dfrac1t=\\sqrt{x+1}+\\sqrt x$ 다.',
          '$\\sqrt x=\\dfrac{1}{2}\\left(\\dfrac1t-t\\right)$ 에서 $dx$ 를 $t$ 로 표현한다.'],
  steps: ['$t=\\sqrt{x+1}-\\sqrt x,\;dx=-\\dfrac{1}{2}\\left(\\dfrac{1}{t^{3}}-\\dfrac1t\\right)dt$',
          '$\\int t^{\\pi}dx=\\dfrac12\\int\\left(t^{\\pi+1}-t^{\\pi-3}\\right)\\dfrac{dt}{t}\\cdot(-1)$ 를 정리',
          '$=\\dfrac12\\left(\\dfrac{t^{\\pi+2}}{\\pi+2}-\\dfrac{t^{\\pi-2}}{\\pi-2}\\right)$']
});
add('monster', '역삼각 배각', 'sin(4*arctan(x))', '-4/(1+x^2)-2*ln(1+x^2)', {
  domain: [-1.5, 1.7],
  hints: ['$\\theta=\\arctan x$ 이면 $\\sin 2\\theta=\\dfrac{2x}{1+x^{2}},\;\\cos 2\\theta=\\dfrac{1-x^{2}}{1+x^{2}}$ 다.',
          '$\\sin 4\\theta=2\\sin 2\\theta\\cos 2\\theta=\\dfrac{4x(1-x^{2})}{(1+x^{2})^{2}}$'],
  steps: ['$\\sin(4\\arctan x)=\\dfrac{4x(1-x^{2})}{(1+x^{2})^{2}}$',
          '$u=1+x^{2}$ 로 두면 $\\int\\dfrac{2(2-u)}{u^{2}}du$',
          '$=-\\dfrac{4}{1+x^{2}}-2\\ln(1+x^{2})$']
});
add('monster', '삼각 치환', '(sin(x)+cos(x))/sqrt(25*sin(x)^2+16*cos(x)^2)',
    'asinh(3*sin(x)/4)/3-asin(3*cos(x)/5)/3', {
  domain: D.trigW,
  hints: ['$25\\sin^{2}+16\\cos^{2}$ 는 $16+9\\sin^{2}$ 이자 $25-9\\cos^{2}$ 다.',
          '$\\cos x\\,dx$ 항에는 앞의 표현을, $\\sin x\\,dx$ 항에는 뒤의 표현을 쓴다.'],
  steps: ['$\\int\\dfrac{\\cos x\\,dx}{\\sqrt{16+9\\sin^{2}x}}=\\dfrac13\\operatorname{arsinh}\\dfrac{3\\sin x}{4}$',
          '$\\int\\dfrac{\\sin x\\,dx}{\\sqrt{25-9\\cos^{2}x}}=-\\dfrac13\\arcsin\\dfrac{3\\cos x}{5}$']
});
add('monster', '역수 치환', 'sqrt(x)/(1+x^2)',
    '(arctan((x-1)/sqrt(2*x))-atanh(sqrt(2*x)/(x+1)))/sqrt(2)', {
  domain: [1.35, 3.4],
  hints: ['$t=\\sqrt x$ 로 두면 $\\int\\dfrac{2t^{2}}{1+t^{4}}dt$ 로 $\\sqrt{\\tan x}$ 문제와 같은 꼴이 된다.',
          '$t^{2}\\pm1$ 로 쪼갠 뒤 $u=t\\mp\\dfrac1t$ 치환을 각각 쓴다.'],
  steps: ['$t=\\sqrt x:\;\\int\\dfrac{2t^{2}}{1+t^{4}}dt$',
          '$=\\int\\dfrac{t^{2}+1}{t^{4}+1}dt+\\int\\dfrac{t^{2}-1}{t^{4}+1}dt$',
          '$\\arctan$ 항과 $\\operatorname{artanh}$ 항이 남는다']
});

// ================================================================== 역쌍곡선함수 보강

// --- 보통: 1차식 대입과 기본 치환
add('medium', '역쌍곡선함수', 'asinh(2*x)', 'x*asinh(2*x)-sqrt(4*x^2+1)/2', {
  domain: [-1.5, 1.7],
  hints: ['$dv=dx$ 로 부분적분한다.', '$\\left(\\operatorname{arsinh}2x\\right)\'=\\dfrac{2}{\\sqrt{1+4x^{2}}}$'],
  steps: ['$=x\\operatorname{arsinh}2x-\\int\\dfrac{2x}{\\sqrt{1+4x^{2}}}dx$',
          '$=x\\operatorname{arsinh}2x-\\dfrac{\\sqrt{4x^{2}+1}}{2}$']
});
add('medium', '역쌍곡선함수', 'acosh(2*x)', 'x*acosh(2*x)-sqrt(4*x^2-1)/2', {
  domain: [0.7, 1.7],
  hints: ['$dv=dx$ 로 부분적분한다.', '$\\left(\\operatorname{arcosh}2x\\right)\'=\\dfrac{2}{\\sqrt{4x^{2}-1}}$'],
  steps: ['$=x\\operatorname{arcosh}2x-\\int\\dfrac{2x}{\\sqrt{4x^{2}-1}}dx$',
          '$=x\\operatorname{arcosh}2x-\\dfrac{\\sqrt{4x^{2}-1}}{2}$']
});
add('medium', '역쌍곡선함수', 'atanh(2*x)', 'x*atanh(2*x)+ln(1-4*x^2)/4', {
  domain: [-0.36, 0.36],
  hints: ['$dv=dx$ 로 부분적분한다.', '$\\left(\\operatorname{artanh}2x\\right)\'=\\dfrac{2}{1-4x^{2}}$'],
  steps: ['$=x\\operatorname{artanh}2x-\\int\\dfrac{2x}{1-4x^{2}}dx$',
          '$=x\\operatorname{artanh}2x+\\dfrac{\\ln(1-4x^{2})}{4}$']
});
add('medium', '역쌍곡선 치환', 'asinh(x)/sqrt(1+x^2)', 'asinh(x)^2/2', {
  domain: [-1.5, 1.7],
  hints: ['$u=\\operatorname{arsinh}x$ 로 두면 $du=\\dfrac{dx}{\\sqrt{1+x^{2}}}$ 다.', '$\\int u\\,du$ 만 남는다.'],
  steps: ['$u=\\operatorname{arsinh}x$', '$\\int u\\,du=\\dfrac{\\operatorname{arsinh}^{2}x}{2}$']
});
add('medium', '역쌍곡선 치환', 'acosh(x)/sqrt(x^2-1)', 'acosh(x)^2/2', {
  domain: D.gt1,
  hints: ['$u=\\operatorname{arcosh}x$ 로 두면 $du=\\dfrac{dx}{\\sqrt{x^{2}-1}}$ 다.', '$\\int u\\,du$ 꼴이다.'],
  steps: ['$u=\\operatorname{arcosh}x$', '$\\int u\\,du=\\dfrac{\\operatorname{arcosh}^{2}x}{2}$']
});
add('medium', '역쌍곡선 치환', 'atanh(x)/(1-x^2)', 'atanh(x)^2/2', {
  domain: D.unit,
  hints: ['$u=\\operatorname{artanh}x$ 로 두면 $du=\\dfrac{dx}{1-x^{2}}$ 다.', '$\\int u\\,du$ 꼴이다.'],
  steps: ['$u=\\operatorname{artanh}x$', '$\\int u\\,du=\\dfrac{\\operatorname{artanh}^{2}x}{2}$']
});

// --- 어려움: 부분적분 조합
add('hard', '역쌍곡선 부분적분', 'x*acosh(x)', '(2*x^2-1)*acosh(x)/4-x*sqrt(x^2-1)/4', {
  domain: D.gt1,
  hints: ['$v=\\dfrac{2x^{2}-1}{4}$ 로 잡으면 남는 적분이 깔끔해진다.',
          '$\\int\\dfrac{2x^{2}-1}{4\\sqrt{x^{2}-1}}dx=\\dfrac{x\\sqrt{x^{2}-1}}{4}$'],
  steps: ['$v=\\dfrac{2x^{2}-1}{4}$ 로 부분적분',
          '$=\\dfrac{(2x^{2}-1)\\operatorname{arcosh}x}{4}-\\dfrac{x\\sqrt{x^{2}-1}}{4}$']
});
add('hard', '역쌍곡선 부분적분', 'x*atanh(x)', '(x^2-1)*atanh(x)/2+x/2', {
  domain: D.unit,
  hints: ['$v=\\dfrac{x^{2}-1}{2}$ 로 잡으면 $\\dfrac{x^{2}-1}{1-x^{2}}=-1$ 로 약분된다.',
          '남는 적분이 $\\dfrac12\\int dx$ 가 된다.'],
  steps: ['$v=\\dfrac{x^{2}-1}{2}$ 로 부분적분',
          '$=\\dfrac{(x^{2}-1)\\operatorname{artanh}x}{2}+\\dfrac x2$']
});
add('hard', '역쌍곡선 부분적분', 'x^2*asinh(x)', 'x^3*asinh(x)/3-(x^2+1)^(3/2)/9+sqrt(x^2+1)/3', {
  domain: [-1.5, 1.7],
  hints: ['$v=\\dfrac{x^{3}}{3}$ 로 부분적분하면 $\\dfrac13\\int\\dfrac{x^{3}}{\\sqrt{1+x^{2}}}dx$ 가 남는다.',
          '$u=1+x^{2}$ 로 두면 $\\dfrac12\\int\\dfrac{u-1}{\\sqrt u}du$ 다.'],
  steps: ['$=\\dfrac{x^{3}\\operatorname{arsinh}x}{3}-\\dfrac13\\int\\dfrac{x^{3}dx}{\\sqrt{1+x^{2}}}$',
          '$\\int\\dfrac{x^{3}dx}{\\sqrt{1+x^{2}}}=\\dfrac{(1+x^{2})^{3/2}}{3}-\\sqrt{1+x^{2}}$']
});
add('hard', '역쌍곡선 부분적분', 'asinh(x)^2', 'x*asinh(x)^2-2*sqrt(1+x^2)*asinh(x)+2*x', {
  domain: [-1.5, 1.7],
  hints: ['부분적분 후 $\\int\\dfrac{2x\\operatorname{arsinh}x}{\\sqrt{1+x^{2}}}dx$ 가 남는다.',
          '$\\left(2\\sqrt{1+x^{2}}\\right)\'=\\dfrac{2x}{\\sqrt{1+x^{2}}}$ 로 한 번 더 부분적분한다.'],
  steps: ['$=x\\operatorname{arsinh}^{2}x-\\int\\dfrac{2x\\operatorname{arsinh}x}{\\sqrt{1+x^{2}}}dx$',
          '$=x\\operatorname{arsinh}^{2}x-2\\sqrt{1+x^{2}}\\operatorname{arsinh}x+2x$']
});
add('hard', '역쌍곡선 부분적분', 'x*asinh(x)/sqrt(1+x^2)', 'sqrt(1+x^2)*asinh(x)-x', {
  domain: [-1.5, 1.7],
  hints: ['$dv=\\dfrac{x\\,dx}{\\sqrt{1+x^{2}}}\\Rightarrow v=\\sqrt{1+x^{2}}$',
          '남는 적분에서 $\\dfrac{\\sqrt{1+x^{2}}}{\\sqrt{1+x^{2}}}=1$ 로 약분된다.'],
  steps: ['$=\\sqrt{1+x^{2}}\\operatorname{arsinh}x-\\int dx$',
          '$=\\sqrt{1+x^{2}}\\operatorname{arsinh}x-x$']
});
add('hard', '역쌍곡선 부분적분', 'x*acosh(x)/sqrt(x^2-1)', 'sqrt(x^2-1)*acosh(x)-x', {
  domain: D.gt1,
  hints: ['$v=\\sqrt{x^{2}-1}$ 로 부분적분한다.', '남는 적분은 $\\int dx$ 다.'],
  steps: ['$=\\sqrt{x^{2}-1}\\operatorname{arcosh}x-\\int dx$', '$=\\sqrt{x^{2}-1}\\operatorname{arcosh}x-x$']
});
add('hard', '역쌍곡선 부분적분', 'atanh(x)/x^2', 'ln(x)-ln(1-x^2)/2-atanh(x)/x', {
  domain: [0.15, 0.8],
  hints: ['$v=-\\dfrac1x$ 로 부분적분한다.', '남는 $\\int\\dfrac{dx}{x(1-x^{2})}=\\ln|x|-\\dfrac12\\ln|1-x^{2}|$'],
  steps: ['$=-\\dfrac{\\operatorname{artanh}x}{x}+\\int\\dfrac{dx}{x(1-x^{2})}$',
          '$\\dfrac{1}{x(1-x^{2})}=\\dfrac1x+\\dfrac{x}{1-x^{2}}$']
});
add('hard', '역쌍곡선 부분적분', 'acosh(x)/x^2', 'atan(sqrt(x^2-1))-acosh(x)/x', {
  domain: D.gt1,
  hints: ['$v=-\\dfrac1x$ 로 부분적분한다.', '남는 $\\int\\dfrac{dx}{x\\sqrt{x^{2}-1}}=\\arctan\\sqrt{x^{2}-1}$'],
  steps: ['$=-\\dfrac{\\operatorname{arcosh}x}{x}+\\int\\dfrac{dx}{x\\sqrt{x^{2}-1}}$',
          '$=\\arctan\\sqrt{x^{2}-1}-\\dfrac{\\operatorname{arcosh}x}{x}$']
});
add('hard', '역쌍곡선 치환', 'asinh(x)^2/sqrt(1+x^2)', 'asinh(x)^3/3', {
  domain: [-1.5, 1.7],
  hints: ['$u=\\operatorname{arsinh}x$ 로 두면 $\\int u^{2}du$ 다.', '거듭제곱 법칙으로 끝난다.'],
  steps: ['$u=\\operatorname{arsinh}x$', '$\\int u^{2}du=\\dfrac{\\operatorname{arsinh}^{3}x}{3}$']
});
add('hard', '역쌍곡선 치환', '1/(sqrt(1+x^2)*asinh(x))', 'ln(asinh(x))', {
  domain: [0.3, 2.6], lnAbs: true,
  hints: ['$u=\\operatorname{arsinh}x$ 로 두면 $\\int\\dfrac{du}{u}$ 다.', '결과는 로그의 로그 꼴이다.'],
  steps: ['$u=\\operatorname{arsinh}x,\;du=\\dfrac{dx}{\\sqrt{1+x^{2}}}$',
          '$\\int\\dfrac{du}{u}=\\ln\\left|\\operatorname{arsinh}x\\right|$']
});
add('hard', '역쌍곡선 치환', '1/(sqrt(x^2+1)*(asinh(x)^2+1))', 'atan(asinh(x))', {
  domain: [-1.5, 1.7],
  hints: ['$u=\\operatorname{arsinh}x$ 로 두면 $\\int\\dfrac{du}{u^{2}+1}$ 다.', '$\\arctan$ 이 남는다.'],
  steps: ['$u=\\operatorname{arsinh}x$', '$\\arctan\\left(\\operatorname{arsinh}x\\right)$']
});
add('hard', '역쌍곡선 부분적분', 'x^3*asinh(x)',
    'x^4*asinh(x)/4-x^3*sqrt(1+x^2)/16+3*x*sqrt(1+x^2)/32-3*asinh(x)/32', {
  domain: [-1.5, 1.7],
  hints: ['$v=\\dfrac{x^{4}}{4}$ 로 부분적분하면 $\\dfrac14\\int\\dfrac{x^{4}}{\\sqrt{1+x^{2}}}dx$ 가 남는다.',
          '$I_{n}=\\dfrac{x^{n-1}\\sqrt{1+x^{2}}}{n}-\\dfrac{n-1}{n}I_{n-2}$ 점화식을 쓴다.'],
  steps: ['$I_{2}=\\dfrac{x\\sqrt{1+x^{2}}}{2}-\\dfrac{\\operatorname{arsinh}x}{2}$',
          '$I_{4}=\\dfrac{x^{3}\\sqrt{1+x^{2}}}{4}-\\dfrac34I_{2}$',
          '$\\dfrac{x^{4}\\operatorname{arsinh}x}{4}-\\dfrac{I_{4}}{4}$ 를 정리한다']
});

// --- 몬스터: 역쌍곡선 항등식과 위장
add('monster', '역쌍곡선 배각', 'asinh(2*x*sqrt(1+x^2))', '2*x*asinh(x)-2*sqrt(1+x^2)', {
  domain: [0.2, 1.6],
  hints: ['$\\sinh 2t=2\\sinh t\\cosh t$ 를 거꾸로 읽는다.',
          '$x=\\sinh t$ 로 두면 피적분함수는 그냥 $2t=2\\operatorname{arsinh}x$ 다.'],
  steps: ['$\\operatorname{arsinh}\\left(2x\\sqrt{1+x^{2}}\\right)=2\\operatorname{arsinh}x$',
          '$2\\int\\operatorname{arsinh}x\\,dx=2x\\operatorname{arsinh}x-2\\sqrt{1+x^{2}}$']
});
add('monster', '역쌍곡선 배각', 'acosh(2*x^2-1)', '2*x*acosh(x)-2*sqrt(x^2-1)', {
  domain: D.gt1,
  hints: ['$\\cosh 2t=2\\cosh^{2}t-1$ 을 거꾸로 읽는다.',
          '$x=\\cosh t\;(t\\ge 0)$ 이면 피적분함수는 $2t=2\\operatorname{arcosh}x$ 다.'],
  steps: ['$\\operatorname{arcosh}(2x^{2}-1)=2\\operatorname{arcosh}x$',
          '$2\\int\\operatorname{arcosh}x\\,dx=2x\\operatorname{arcosh}x-2\\sqrt{x^{2}-1}$']
});
add('monster', '역쌍곡선 배각', 'atanh(2*x/(1+x^2))', '2*x*atanh(x)+ln(1-x^2)', {
  domain: D.unit,
  hints: ['쌍곡선 배각공식 $\\tanh 2t=\\dfrac{2\\tanh t}{1+\\tanh^{2}t}$ 를 거꾸로 읽는다.',
          '$x=\\tanh t$ 로 두면 피적분함수가 그냥 $2t=2\\operatorname{artanh}x$ 가 된다.'],
  steps: ['$\\operatorname{artanh}\\dfrac{2x}{1+x^{2}}=2\\operatorname{artanh}x$',
          '$2\\int\\operatorname{artanh}x\\,dx=2x\\operatorname{artanh}x+\\ln(1-x^{2})$']
});
add('monster', '역쌍곡선 치환', 'asinh(x)/(1+x^2)^(3/2)', 'x*asinh(x)/sqrt(1+x^2)-ln(1+x^2)/2', {
  domain: [0.2, 2.4],
  hints: ['$x=\\sinh t$ 로 두면 $\\int\\dfrac{t}{\\cosh^{2}t}dt$ 로 바뀐다.',
          '$\\int t\\operatorname{sech}^{2}t\\,dt=t\\tanh t-\\ln\\cosh t$'],
  steps: ['$x=\\sinh t,\;dx=\\cosh t\\,dt$', '$\\int t\\operatorname{sech}^{2}t\\,dt=t\\tanh t-\\ln\\cosh t$',
          '$\\tanh t=\\dfrac{x}{\\sqrt{1+x^{2}}},\;\\cosh t=\\sqrt{1+x^{2}}$']
});
add('monster', '역쌍곡선 치환', 'atanh(x)/(1-x^2)^(3/2)', 'x*atanh(x)/sqrt(1-x^2)-1/sqrt(1-x^2)', {
  domain: D.unit,
  hints: ['$x=\\tanh t$ 로 두면 $\\int t\\cosh t\\,dt$ 로 바뀐다.',
          '$\\int t\\cosh t\\,dt=t\\sinh t-\\cosh t$'],
  steps: ['$x=\\tanh t,\;dx=\\operatorname{sech}^{2}t\\,dt,\;(1-x^{2})^{3/2}=\\operatorname{sech}^{3}t$',
          '$\\int t\\cosh t\\,dt=t\\sinh t-\\cosh t$',
          '$\\sinh t=\\dfrac{x}{\\sqrt{1-x^{2}}},\;\\cosh t=\\dfrac{1}{\\sqrt{1-x^{2}}}$']
});
add('monster', '역쌍곡선 치환', 'acosh(x)/(x^2-1)^(3/2)', 'ln(x^2-1)/2-x*acosh(x)/sqrt(x^2-1)', {
  domain: D.gt1,
  hints: ['$x=\\cosh t$ 로 두면 $\\int\\dfrac{t}{\\sinh^{2}t}dt$ 로 바뀐다.',
          '$\\int t\\operatorname{csch}^{2}t\\,dt=-t\\coth t+\\ln|\\sinh t|$'],
  steps: ['$x=\\cosh t$', '$-t\\coth t+\\ln\\sinh t$',
          '$\\coth t=\\dfrac{x}{\\sqrt{x^{2}-1}},\;\\sinh t=\\sqrt{x^{2}-1}$']
});
add('monster', '역쌍곡선 부분적분', 'asinh(sqrt(x))', '(2*x+1)*asinh(sqrt(x))/2-sqrt(x^2+x)/2', {
  domain: [0.3, 3.0],
  hints: ['$dv=dx$ 로 부분적분하면 $\\dfrac12\\int\\sqrt{\\dfrac{x}{1+x}}dx$ 가 남는다.',
          '$u=\\sqrt x$ 로 다시 치환하면 $2\\int\\dfrac{u^{2}}{\\sqrt{1+u^{2}}}du$ 다.'],
  steps: ['$=x\\operatorname{arsinh}\\sqrt x-\\dfrac12\\int\\dfrac{\\sqrt x}{\\sqrt{1+x}}dx$',
          '$\\int\\sqrt{\\dfrac{x}{1+x}}dx=\\sqrt{x(1+x)}-\\operatorname{arsinh}\\sqrt x$',
          '정리하면 $\\dfrac{(2x+1)\\operatorname{arsinh}\\sqrt x}{2}-\\dfrac{\\sqrt{x^{2}+x}}{2}$']
});
add('monster', '역쌍곡선 부분적분', 'atanh(sqrt(x))', '(x-1)*atanh(sqrt(x))+sqrt(x)', {
  domain: [0.05, 0.82],
  hints: ['$v=x-1$ 로 잡으면 남는 적분이 크게 줄어든다.',
          '$\\left(\\operatorname{artanh}\\sqrt x\\right)\'=\\dfrac{1}{2\\sqrt x(1-x)}$'],
  steps: ['$v=x-1$ 로 부분적분: $(x-1)\\operatorname{artanh}\\sqrt x+\\int\\dfrac{dx}{2\\sqrt x}$',
          '$=(x-1)\\operatorname{artanh}\\sqrt x+\\sqrt x$']
});
add('monster', '역쌍곡선 위장', 'atanh(1/x)', 'x*atanh(1/x)+ln(x^2-1)/2', {
  domain: D.gt1, lnAbs: true,
  hints: ['$\\operatorname{artanh}\\dfrac1x=\\dfrac12\\ln\\dfrac{x+1}{x-1}$ 이므로 $|x|>1$ 에서 정의된다.',
          '$\\left(\\operatorname{artanh}\\dfrac1x\\right)\'=-\\dfrac{1}{x^{2}-1}$'],
  steps: ['$dv=dx$ 로 부분적분: $x\\operatorname{artanh}\\dfrac1x+\\int\\dfrac{x\\,dx}{x^{2}-1}$',
          '$=x\\operatorname{artanh}\\dfrac1x+\\dfrac{\\ln|x^{2}-1|}{2}$']
});
add('monster', '역쌍곡선 지수', 'e^x*atanh(e^x)', 'e^x*atanh(e^x)+ln(1-e^(2*x))/2', {
  domain: [-2.2, -0.3],
  hints: ['$u=e^{x}$ 로 두면 $\\int\\operatorname{artanh}u\\,du$ 다.',
          '$\\int\\operatorname{artanh}u\\,du=u\\operatorname{artanh}u+\\dfrac{\\ln(1-u^{2})}{2}$'],
  steps: ['$u=e^{x},\;du=e^{x}dx$', '$\\int\\operatorname{artanh}u\\,du=u\\operatorname{artanh}u+\\dfrac{\\ln(1-u^{2})}{2}$',
          '$u$ 를 되돌린다']
});
add('monster', '역쌍곡선 부분적분', 'asinh(x)*sqrt(1+x^2)',
    'x*sqrt(1+x^2)*asinh(x)/2+asinh(x)^2/4-x^2/4', {
  domain: [0.2, 2.0],
  hints: ['$v=\\dfrac{x\\sqrt{1+x^{2}}+\\operatorname{arsinh}x}{2}$ 로 부분적분한다.',
          '남는 적분은 $\\int\\left(\\dfrac x2+\\dfrac{\\operatorname{arsinh}x}{2\\sqrt{1+x^{2}}}\\right)dx$ 다.'],
  steps: ['$v=\\int\\sqrt{1+x^{2}}dx=\\dfrac{x\\sqrt{1+x^{2}}+\\operatorname{arsinh}x}{2}$',
          '$\\int\\dfrac{v}{\\sqrt{1+x^{2}}}dx=\\dfrac{x^{2}}{4}+\\dfrac{\\operatorname{arsinh}^{2}x}{4}$',
          '두 결과를 뺀다']
});

// ================================================================== 어려움 보강
// 한 가지 기법을 그대로 쓰면 끝나는 문항은 '보통' 으로 내렸으므로,
// 이 자리에는 두세 단계를 엮어야 풀리는 것들을 채운다.

// --- 고차 유리식: 점화·부분분수를 두 번 이상
add('hard', '유리식 점화', '1/(x^2+4)^2', 'x/(8*(x^2+4))+arctan(x/2)/16', {
  domain: [-1.5, 1.7],
  hints: ['$\\int\\dfrac{dx}{(x^{2}+a^{2})^{2}}=\\dfrac{x}{2a^{2}(x^{2}+a^{2})}+\\dfrac{\\arctan(x/a)}{2a^{3}}$',
          '$a=2$ 이므로 분모에 $8$ 과 $16$ 이 나온다.'],
  steps: ['$x=2\\tan\\theta$ 로 두면 $\\dfrac18\\int\\cos^{2}\\theta\\,d\\theta$',
          '$=\\dfrac{x}{8(x^{2}+4)}+\\dfrac{\\arctan(x/2)}{16}$']
});
add('hard', '유리식 점화', 'x^2/(x^2+4)^2', 'arctan(x/2)/4-x/(2*(x^2+4))', {
  domain: [-1.5, 1.7],
  hints: ['$\\dfrac{x^{2}}{(x^{2}+4)^{2}}=\\dfrac{1}{x^{2}+4}-\\dfrac{4}{(x^{2}+4)^{2}}$ 로 쪼갠다.',
          '두 번째 항에 앞 문제의 결과를 그대로 쓴다.'],
  steps: ['$\\dfrac{1}{x^{2}+4}$ 는 $\\dfrac{\\arctan(x/2)}{2}$',
          '$-4\\left[\\dfrac{x}{8(x^{2}+4)}+\\dfrac{\\arctan(x/2)}{16}\\right]$ 를 더한다']
});
add('hard', '유리식 점화', '1/(x^2+1)^3',
    'x/(4*(x^2+1)^2)+3*x/(8*(x^2+1))+3*arctan(x)/8', {
  domain: [-1.5, 1.7],
  hints: ['$I_{n}=\\dfrac{x}{2(n-1)(x^{2}+1)^{n-1}}+\\dfrac{2n-3}{2n-2}I_{n-1}$ 점화식을 쓴다.',
          '$I_{2}=\\dfrac{x}{2(x^{2}+1)}+\\dfrac{\\arctan x}{2}$ 에서 한 단계 올린다.'],
  steps: ['$I_{3}=\\dfrac{x}{4(x^{2}+1)^{2}}+\\dfrac34 I_{2}$',
          '$=\\dfrac{x}{4(x^{2}+1)^{2}}+\\dfrac{3x}{8(x^{2}+1)}+\\dfrac{3\\arctan x}{8}$']
});
add('hard', '가분수 나눗셈', 'x^4/(x^2+1)^2', 'x-3*arctan(x)/2+x/(2*(x^2+1))', {
  domain: [-1.5, 1.7],
  hints: ['$\\dfrac{x^{4}}{(x^{2}+1)^{2}}=1-\\dfrac{2x^{2}+1}{(x^{2}+1)^{2}}$ 로 먼저 나눈다.',
          '$\\dfrac{2x^{2}+1}{(x^{2}+1)^{2}}$ 를 다시 두 조각으로 나눈다.'],
  steps: ['$\\int\\dfrac{2x^{2}+1}{(x^{2}+1)^{2}}dx=\\dfrac{3\\arctan x}{2}-\\dfrac{x}{2(x^{2}+1)}$',
          '$=x-\\dfrac{3\\arctan x}{2}+\\dfrac{x}{2(x^{2}+1)}$']
});
add('hard', '가분수 나눗셈', 'x^5/(x^2+1)', 'x^4/4-x^2/2+ln(1+x^2)/2', {
  domain: D.poly,
  hints: ['먼저 다항식 나눗셈: $\\dfrac{x^{5}}{x^{2}+1}=x^{3}-x+\\dfrac{x}{x^{2}+1}$',
          '마지막 항만 로그가 된다.'],
  steps: ['$x^{3}-x+\\dfrac{x}{x^{2}+1}$ 로 나눈다', '$=\\dfrac{x^{4}}{4}-\\dfrac{x^{2}}{2}+\\dfrac{\\ln(1+x^{2})}{2}$']
});
add('hard', '부분분수', 'x^2/(x^4-1)', 'ln((x-1)/(x+1))/4+arctan(x)/2', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['$\\dfrac{x^{2}}{x^{4}-1}=\\dfrac12\\left(\\dfrac{1}{x^{2}-1}+\\dfrac{1}{x^{2}+1}\\right)$',
          '두 항 모두 적분표에 있다.'],
  steps: ['$x^{4}-1=(x^{2}-1)(x^{2}+1)$ 로 쪼갠다',
          '$=\\dfrac14\\ln\\left|\\dfrac{x-1}{x+1}\\right|+\\dfrac{\\arctan x}{2}$']
});
add('hard', '부분분수', '1/(x^4-16)', 'ln((x-2)/(x+2))/32-arctan(x/2)/16', {
  domain: [2.4, 4.6], lnAbs: true,
  hints: ['$x^{4}-16=(x^{2}-4)(x^{2}+4)$ 로 인수분해한다.',
          '$\\dfrac{1}{x^{4}-16}=\\dfrac18\\left(\\dfrac{1}{x^{2}-4}-\\dfrac{1}{x^{2}+4}\\right)$'],
  steps: ['부분분수로 쪼갠다',
          '$=\\dfrac{1}{32}\\ln\\left|\\dfrac{x-2}{x+2}\\right|-\\dfrac{\\arctan(x/2)}{16}$']
});
add('hard', '부분분수', '1/((x^2+1)*(x^2+4))', 'arctan(x)/3-arctan(x/2)/6', {
  domain: [-1.5, 1.7],
  hints: ['$t=x^{2}$ 로 보고 $\\dfrac{1}{(t+1)(t+4)}=\\dfrac13\\left(\\dfrac{1}{t+1}-\\dfrac{1}{t+4}\\right)$',
          '되돌리면 $\\arctan$ 두 개가 남는다.'],
  steps: ['$\\dfrac13\\left(\\dfrac{1}{x^{2}+1}-\\dfrac{1}{x^{2}+4}\\right)$',
          '$=\\dfrac{\\arctan x}{3}-\\dfrac{\\arctan(x/2)}{6}$']
});
add('hard', '부분분수', 'x^2/((x^2+1)*(x^2+4))', '2*arctan(x/2)/3-arctan(x)/3', {
  domain: [-1.5, 1.7],
  hints: ['$t=x^{2}$ 로 보고 $\\dfrac{t}{(t+1)(t+4)}$ 를 쪼갠다.', '계수는 $-\\dfrac13$ 과 $\\dfrac43$ 이다.'],
  steps: ['$-\\dfrac13\\cdot\\dfrac{1}{x^{2}+1}+\\dfrac43\\cdot\\dfrac{1}{x^{2}+4}$',
          '$=-\\dfrac{\\arctan x}{3}+\\dfrac{2\\arctan(x/2)}{3}$']
});
add('hard', '치환+부분분수', 'x/((x^2+1)*(x^2+4))', 'ln((x^2+1)/(x^2+4))/6', {
  domain: D.poly,
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\int\\dfrac{du}{(u+1)(u+4)}$ 다.',
          '$\\dfrac{1}{(u+1)(u+4)}=\\dfrac13\\left(\\dfrac{1}{u+1}-\\dfrac{1}{u+4}\\right)$'],
  steps: ['$u=x^{2}$', '$\\dfrac16\\ln\\dfrac{x^{2}+1}{x^{2}+4}$']
});
add('hard', '중근 부분분수', '1/((x-1)^2*(x+1))', 'ln((x+1)/(x-1))/4-1/(2*(x-1))', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['중근이 있으므로 $\\dfrac{A}{x-1}+\\dfrac{B}{(x-1)^{2}}+\\dfrac{C}{x+1}$ 로 놓는다.',
          '$B=\\dfrac12,\;C=\\dfrac14,\;A=-\\dfrac14$'],
  steps: ['부분분수로 쪼갠다',
          '$=-\\dfrac{\\ln|x-1|}{4}-\\dfrac{1}{2(x-1)}+\\dfrac{\\ln|x+1|}{4}$']
});
add('hard', '부분분수', '1/(x*(x+1)*(x+2))', 'ln(x)/2-ln(x+1)+ln(x+2)/2', {
  domain: D.pos, lnAbs: true,
  hints: ['가리기(cover-up)로 $x=0,-1,-2$ 를 차례로 대입한다.', '계수는 $\\dfrac12,\\,-1,\\,\\dfrac12$ 다.'],
  steps: ['$\\dfrac{1/2}{x}-\\dfrac{1}{x+1}+\\dfrac{1/2}{x+2}$', '각 항을 로그로 적분']
});
add('hard', '부분분수', '1/(x*(1+x^2)^2)', 'ln(x)-ln(1+x^2)/2+1/(2*(1+x^2))', {
  domain: D.pos, lnAbs: true,
  hints: ['$\\dfrac{1}{x(1+x^{2})^{2}}=\\dfrac1x-\\dfrac{x}{1+x^{2}}-\\dfrac{x}{(1+x^{2})^{2}}$',
          '마지막 항은 $u=1+x^{2}$ 로 바로 적분된다.'],
  steps: ['세 조각으로 쪼갠다',
          '$=\\ln|x|-\\dfrac{\\ln(1+x^{2})}{2}+\\dfrac{1}{2(1+x^{2})}$']
});

// --- 완전제곱 + 근호
add('hard', '완전제곱 근호', 'sqrt(x^2+2*x+5)',
    '(x+1)*sqrt(x^2+2*x+5)/2+2*asinh((x+1)/2)', {
  domain: [0.2, 2.8],
  hints: ['$x^{2}+2x+5=(x+1)^{2}+4$ 로 완전제곱한다.',
          '$\\int\\sqrt{u^{2}+a^{2}}du=\\dfrac{u\\sqrt{u^{2}+a^{2}}}{2}+\\dfrac{a^{2}}{2}\\operatorname{arsinh}\\dfrac ua$'],
  steps: ['$u=x+1,\;a=2$', '$=\\dfrac{(x+1)\\sqrt{x^{2}+2x+5}}{2}+2\\operatorname{arsinh}\\dfrac{x+1}{2}$']
});
add('hard', '완전제곱 근호', 'sqrt(x^2-4*x+3)',
    '(x-2)*sqrt(x^2-4*x+3)/2-acosh(x-2)/2', {
  domain: [3.4, 6.0],
  hints: ['$x^{2}-4x+3=(x-2)^{2}-1$ 로 완전제곱한다.',
          '$\\int\\sqrt{u^{2}-1}\\,du=\\dfrac{u\\sqrt{u^{2}-1}}{2}-\\dfrac{\\operatorname{arcosh}u}{2}$'],
  steps: ['$u=x-2$', '$=\\dfrac{(x-2)\\sqrt{x^{2}-4x+3}}{2}-\\dfrac{\\operatorname{arcosh}(x-2)}{2}$']
});

// --- 삼각 치환에서 로그가 나오는 것들
add('hard', '삼각 치환', '1/(x*sqrt(1-x^2))', 'ln(x/(1+sqrt(1-x^2)))', {
  domain: [0.2, 0.85], lnAbs: true,
  hints: ['$x=\\sin\\theta$ 로 두면 $\\int\\csc\\theta\\,d\\theta$ 가 된다.',
          '$\\int\\csc\\theta\\,d\\theta=\\ln\\left|\\tan\\dfrac\\theta2\\right|$ 를 $x$ 로 되돌린다.'],
  steps: ['$x=\\sin\\theta$', '$\\ln\\left|\\tan\\dfrac\\theta2\\right|=\\ln\\left|\\dfrac{x}{1+\\sqrt{1-x^{2}}}\\right|$']
});
add('hard', '삼각 치환', 'sqrt(1-x^2)/x', 'sqrt(1-x^2)+ln(x/(1+sqrt(1-x^2)))', {
  domain: [0.2, 0.85], lnAbs: true,
  hints: ['$\\dfrac{\\sqrt{1-x^{2}}}{x}=\\dfrac{1-x^{2}}{x\\sqrt{1-x^{2}}}=\\dfrac{1}{x\\sqrt{1-x^{2}}}-\\dfrac{x}{\\sqrt{1-x^{2}}}$',
          '앞 항은 앞 문제, 뒤 항은 $u=1-x^{2}$ 치환이다.'],
  steps: ['두 조각으로 쪼갠다',
          '$=\\sqrt{1-x^{2}}+\\ln\\left|\\dfrac{x}{1+\\sqrt{1-x^{2}}}\\right|$']
});
add('hard', '삼각 치환', 'sqrt(1-x^2)/x^2', '-sqrt(1-x^2)/x-arcsin(x)', {
  domain: [0.2, 0.85],
  hints: ['$x=\\sin\\theta$ 로 두면 $\\int\\cot^{2}\\theta\\,d\\theta$ 가 된다.',
          '$\\cot^{2}=\\csc^{2}-1$'],
  steps: ['$x=\\sin\\theta$', '$-\\cot\\theta-\\theta=-\\dfrac{\\sqrt{1-x^{2}}}{x}-\\arcsin x$']
});
add('hard', '역삼각 부분적분', 'arcsin(x)/x^2', 'ln(x/(1+sqrt(1-x^2)))-arcsin(x)/x', {
  domain: [0.2, 0.85], lnAbs: true,
  hints: ['$v=-\\dfrac1x$ 로 부분적분하면 $\\int\\dfrac{dx}{x\\sqrt{1-x^{2}}}$ 가 남는다.',
          '그 적분은 $\\ln\\left|\\dfrac{x}{1+\\sqrt{1-x^{2}}}\\right|$ 다.'],
  steps: ['$=-\\dfrac{\\arcsin x}{x}+\\int\\dfrac{dx}{x\\sqrt{1-x^{2}}}$',
          '두 결과를 합친다']
});
add('hard', '쌍곡선 치환', 'x^2/sqrt(x^2+1)', 'x*sqrt(x^2+1)/2-asinh(x)/2', {
  domain: [0.2, 2.4],
  hints: ['$x=\\sinh t$ 로 두면 $\\int\\sinh^{2}t\\,dt$ 다.', '$\\sinh^{2}t=\\dfrac{\\cosh 2t-1}{2}$'],
  steps: ['$x=\\sinh t$', '$\\dfrac{\\sinh 2t}{4}-\\dfrac t2=\\dfrac{x\\sqrt{x^{2}+1}}{2}-\\dfrac{\\operatorname{arsinh}x}{2}$']
});
add('hard', '쌍곡선 치환', 'x^2/sqrt(x^2-1)', 'x*sqrt(x^2-1)/2+acosh(x)/2', {
  domain: D.gt1,
  hints: ['$x=\\cosh t$ 로 두면 $\\int\\cosh^{2}t\\,dt$ 다.', '$\\cosh^{2}t=\\dfrac{\\cosh 2t+1}{2}$'],
  steps: ['$x=\\cosh t$', '$=\\dfrac{x\\sqrt{x^{2}-1}}{2}+\\dfrac{\\operatorname{arcosh}x}{2}$']
});

// --- 고차 삼각
add('hard', '삼각함수 짝수차', 'sin(x)^6',
    '5*x/16-15*sin(2*x)/64+3*sin(4*x)/64-sin(6*x)/192', {
  domain: D.trigW,
  hints: ['반각공식을 세 번 적용해 $\\cos 2x,\\cos 4x,\\cos 6x$ 만 남긴다.',
          '$\\sin^{6}x=\\dfrac{10-15\\cos 2x+6\\cos 4x-\\cos 6x}{32}$'],
  steps: ['$\\sin^{6}x=\\dfrac{10-15\\cos 2x+6\\cos 4x-\\cos 6x}{32}$', '항별로 적분한다']
});
add('hard', '삼각함수 짝수차', 'cos(x)^6',
    '5*x/16+15*sin(2*x)/64+3*sin(4*x)/64+sin(6*x)/192', {
  domain: D.trigW,
  hints: ['$\\cos^{6}x=\\dfrac{10+15\\cos 2x+6\\cos 4x+\\cos 6x}{32}$',
          '$\\sin^{6}$ 과 홀수 항의 부호만 다르다.'],
  steps: ['반각공식을 세 번 적용', '항별로 적분한다']
});
add('hard', '삼각함수 고차', 'tan(x)^6', 'tan(x)^5/5-tan(x)^3/3+tan(x)-x', {
  domain: D.trig,
  hints: ['$\\tan^{6}=\\tan^{4}(\\sec^{2}-1)$ 로 두 단계 내린다.', '$\\int\\tan^{2}=\\tan x-x$'],
  steps: ['$\\int\\tan^{6}=\\dfrac{\\tan^{5}}{5}-\\int\\tan^{4}$',
          '$\\int\\tan^{4}=\\dfrac{\\tan^{3}}{3}-\\tan x+x$']
});
add('hard', '삼각함수 고차', 'sec(x)^6', 'tan(x)+2*tan(x)^3/3+tan(x)^5/5', {
  domain: D.trig,
  hints: ['$\\sec^{6}=\\sec^{2}(1+\\tan^{2})^{2}$ 로 쓴다.', '$u=\\tan x$ 로 두고 전개한다.'],
  steps: ['$u=\\tan x$', '$\\int(1+u^{2})^{2}du=u+\\dfrac{2u^{3}}{3}+\\dfrac{u^{5}}{5}$']
});
add('hard', '삼각함수 짝수차', 'sin(x)^4*cos(x)^2',
    'x/16-sin(2*x)/64-sin(4*x)/64+sin(6*x)/192', {
  domain: D.trigW,
  hints: ['$\\sin^{4}\\cos^{2}=\\dfrac{(1-\\cos 2x)^{2}(1+\\cos 2x)}{8}$ 로 시작한다.',
          '정리하면 $\\dfrac{2-\\cos 2x-2\\cos 4x+\\cos 6x}{32}$ 다.'],
  steps: ['반각·곱합 공식을 섞어 쓴다', '항별로 적분한다']
});
add('hard', '삼각 유리식', '1/(1+cos(x)^2)', 'atan(tan(x)/sqrt(2))/sqrt(2)', {
  domain: D.trig,
  hints: ['분자·분모를 $\\cos^{2}x$ 로 나누면 $\\dfrac{\\sec^{2}x}{\\sec^{2}x+1}$ 이다.',
          '$u=\\tan x$ 로 두면 $\\int\\dfrac{du}{u^{2}+2}$'],
  steps: ['$\\dfrac{\\sec^{2}x}{\\tan^{2}x+2}$', '$u=\\tan x:\;\\dfrac{1}{\\sqrt2}\\arctan\\dfrac{\\tan x}{\\sqrt2}$']
});
add('hard', '삼각 유리식', '1/(1+sin(x)^2)', 'atan(sqrt(2)*tan(x))/sqrt(2)', {
  domain: D.trig,
  hints: ['$\\cos^{2}x$ 로 나누면 $\\dfrac{\\sec^{2}x}{1+2\\tan^{2}x}$ 다.', '$u=\\tan x$ 로 둔다.'],
  steps: ['$u=\\tan x$', '$\\int\\dfrac{du}{1+2u^{2}}=\\dfrac{1}{\\sqrt2}\\arctan(\\sqrt2\\tan x)$']
});
add('hard', '삼각 유리식', '1/(2+3*cos(x)^2)', 'atan(sqrt(2/5)*tan(x))/sqrt(10)', {
  domain: D.trig,
  hints: ['$\\cos^{2}x$ 로 나누면 $\\dfrac{\\sec^{2}x}{2\\tan^{2}x+5}$ 다.', '$u=\\tan x$ 로 둔다.'],
  steps: ['$u=\\tan x$', '$\\int\\dfrac{du}{2u^{2}+5}=\\dfrac{1}{\\sqrt{10}}\\arctan\\left(\\sqrt{\\dfrac25}\\tan x\\right)$']
});
add('hard', '반각 항등식', 'sqrt(1+cos(x))', '2*sqrt(2)*sin(x/2)', {
  domain: [0.25, 2.85],
  hints: ['$1+\\cos x=2\\cos^{2}\\dfrac x2$ 를 쓴다.', '$\\sqrt{1+\\cos x}=\\sqrt2\\cos\\dfrac x2$ (구간에서 양수)'],
  steps: ['$\\sqrt2\\int\\cos\\dfrac x2\\,dx$', '$=2\\sqrt2\\sin\\dfrac x2$']
});
add('hard', '반각 항등식', 'sqrt(1-cos(x))', '-2*sqrt(2)*cos(x/2)', {
  domain: [0.25, 2.85],
  hints: ['$1-\\cos x=2\\sin^{2}\\dfrac x2$ 를 쓴다.', '$\\sqrt{1-\\cos x}=\\sqrt2\\sin\\dfrac x2$'],
  steps: ['$\\sqrt2\\int\\sin\\dfrac x2\\,dx$', '$=-2\\sqrt2\\cos\\dfrac x2$']
});
add('hard', '치환적분', 'sin(x)/(1+cos(x)^2)', '-arctan(cos(x))', {
  domain: D.trigW,
  hints: ['$u=\\cos x$ 로 두면 $du=-\\sin x\\,dx$ 다.', '$-\\int\\dfrac{du}{1+u^{2}}$'],
  steps: ['$u=\\cos x$', '$-\\arctan(\\cos x)$']
});
add('hard', '치환적분', 'cos(x)/sqrt(1+sin(x)^2)', 'asinh(sin(x))', {
  domain: D.trigW,
  hints: ['$u=\\sin x$ 로 둔다.', '$\\int\\dfrac{du}{\\sqrt{1+u^{2}}}=\\operatorname{arsinh}u$'],
  steps: ['$u=\\sin x$', '$\\operatorname{arsinh}(\\sin x)$']
});
add('hard', '치환적분', 'sin(x)*cos(x)/sqrt(1+sin(x)^4)', 'asinh(sin(x)^2)/2', {
  domain: [0.25, 1.3],
  hints: ['$u=\\sin^{2}x$ 로 두면 $du=2\\sin x\\cos x\\,dx$ 다.',
          '$\\dfrac12\\int\\dfrac{du}{\\sqrt{1+u^{2}}}$'],
  steps: ['$u=\\sin^{2}x$', '$\\dfrac{\\operatorname{arsinh}(\\sin^{2}x)}{2}$']
});
add('hard', '부분적분', 'x*sin(x)^2', 'x^2/4-x*sin(2*x)/4-cos(2*x)/8', {
  domain: D.trigW,
  hints: ['$\\sin^{2}x=\\dfrac{1-\\cos 2x}{2}$ 로 먼저 내린다.',
          '$\\int x\\cos 2x\\,dx$ 를 부분적분한다.'],
  steps: ['$\\dfrac12\\int x\\,dx-\\dfrac12\\int x\\cos 2x\\,dx$',
          '$=\\dfrac{x^{2}}{4}-\\dfrac{x\\sin 2x}{4}-\\dfrac{\\cos 2x}{8}$']
});
add('hard', '부분적분', 'x*tan(x)^2', 'x*tan(x)+ln(cos(x))-x^2/2', {
  domain: D.trig, lnAbs: true,
  hints: ['$\\tan^{2}=\\sec^{2}-1$ 로 쪼갠다.', '$\\int x\\sec^{2}x\\,dx=x\\tan x+\\ln|\\cos x|$'],
  steps: ['$\\int x\\sec^{2}x\\,dx-\\int x\\,dx$', '$=x\\tan x+\\ln|\\cos x|-\\dfrac{x^{2}}{2}$']
});

// --- 지수·로그
add('hard', '지수 치환', 'e^x/(1+e^x)^2', '-1/(1+e^x)', {
  domain: [-1.5, 1.7],
  hints: ['$u=1+e^{x}$ 로 두면 $\\int u^{-2}du$ 다.', '$\\int u^{-2}du=-\\dfrac1u$'],
  steps: ['$u=1+e^{x}$', '$-\\dfrac{1}{1+e^{x}}$']
});
add('hard', '지수 치환', 'e^(2*x)/(1+e^x)^2', 'ln(1+e^x)+1/(1+e^x)', {
  domain: [-1.5, 1.7],
  hints: ['$u=e^{x}$ 로 두면 $\\int\\dfrac{u}{(1+u)^{2}}du$ 다.',
          '$\\dfrac{u}{(1+u)^{2}}=\\dfrac{1}{1+u}-\\dfrac{1}{(1+u)^{2}}$'],
  steps: ['$u=e^{x}$', '$\\ln(1+u)+\\dfrac{1}{1+u}$']
});
add('hard', '지수 유리식', '1/(e^x-1)', 'ln(1-e^(-x))', {
  domain: [0.35, 2.4], lnAbs: true,
  hints: ['분자·분모를 $e^{x}$ 로 나누면 $\\dfrac{e^{-x}}{1-e^{-x}}$ 다.',
          '$u=1-e^{-x}$ 로 두면 $du=e^{-x}dx$'],
  steps: ['$\\dfrac{e^{-x}}{1-e^{-x}}$', '$\\ln\\left|1-e^{-x}\\right|$']
});
add('hard', '지수 치환', 'sqrt(e^x-1)', '2*sqrt(e^x-1)-2*arctan(sqrt(e^x-1))', {
  domain: [0.35, 2.2],
  hints: ['$u=\\sqrt{e^{x}-1}$ 로 두면 $dx=\\dfrac{2u\\,du}{u^{2}+1}$ 다.',
          '$\\dfrac{u^{2}}{u^{2}+1}=1-\\dfrac{1}{u^{2}+1}$'],
  steps: ['$u=\\sqrt{e^{x}-1},\;e^{x}=u^{2}+1$',
          '$2\\int\\dfrac{u^{2}}{u^{2}+1}du=2u-2\\arctan u$']
});
add('hard', '지수 부분적분', 'e^x*ln(1+e^x)', '(1+e^x)*ln(1+e^x)-e^x', {
  domain: [-1.2, 1.6],
  hints: ['$u=e^{x}$ 로 두면 $\\int\\ln(1+u)\\,du$ 다.',
          '$\\int\\ln(1+u)du=(1+u)\\ln(1+u)-u$'],
  steps: ['$u=e^{x}$', '$(1+e^{x})\\ln(1+e^{x})-e^{x}$']
});
add('hard', '로그 부분적분', 'x*ln(1+x^2)', '(1+x^2)*ln(1+x^2)/2-x^2/2', {
  domain: D.poly,
  hints: ['$u=1+x^{2}$ 로 두면 $\\dfrac12\\int\\ln u\\,du$ 다.', '$\\int\\ln u\\,du=u\\ln u-u$'],
  steps: ['$u=1+x^{2}$', '$\\dfrac{(1+x^{2})\\ln(1+x^{2})}{2}-\\dfrac{x^{2}}{2}$']
});
add('hard', '로그 분해', 'ln(x^2+x)', 'x*ln(x)+(1+x)*ln(1+x)-2*x', {
  domain: D.pos,
  hints: ['$\\ln(x^{2}+x)=\\ln x+\\ln(1+x)$ 로 먼저 쪼갠다.',
          '$\\int\\ln x\\,dx=x\\ln x-x$, $\\int\\ln(1+x)dx=(1+x)\\ln(1+x)-x$'],
  steps: ['로그를 둘로 쪼갠다', '각각을 부분적분한다']
});
add('hard', '로그 치환', 'ln(x)*ln(ln(x))/x', 'ln(x)^2*ln(ln(x))/2-ln(x)^2/4', {
  domain: [1.4, 4.2],
  hints: ['$u=\\ln x$ 로 두면 $\\int u\\ln u\\,du$ 다.',
          '$\\int u\\ln u\\,du=\\dfrac{u^{2}\\ln u}{2}-\\dfrac{u^{2}}{4}$'],
  steps: ['$u=\\ln x$', '$\\dfrac{\\ln^{2}x\\,\\ln\\ln x}{2}-\\dfrac{\\ln^{2}x}{4}$']
});
add('hard', '유리화', '1/(sqrt(x)+sqrt(x+1))', '2*((x+1)^(3/2)-x^(3/2))/3', {
  domain: D.pos,
  hints: ['분모를 유리화하면 분모가 $1$ 이 된다.', '$\\dfrac{1}{\\sqrt x+\\sqrt{x+1}}=\\sqrt{x+1}-\\sqrt x$'],
  steps: ['유리화한다', '$\\int(\\sqrt{x+1}-\\sqrt x)dx=\\dfrac{2(x+1)^{3/2}-2x^{3/2}}{3}$']
});
add('hard', '분수 지수 치환', '1/(x^(1/3)*(1+x^(2/3)))', '3*ln(1+x^(2/3))/2', {
  domain: D.pos,
  hints: ['$u=x^{1/3}$ 로 두면 $dx=3u^{2}du$ 다.', '$3\\int\\dfrac{u}{1+u^{2}}du$'],
  steps: ['$u=x^{1/3}$', '$\\dfrac32\\ln(1+u^{2})=\\dfrac32\\ln(1+x^{2/3})$']
});
add('hard', '치환적분', 'arctan(x)^2/(1+x^2)', 'arctan(x)^3/3', {
  domain: D.all,
  hints: ['$u=\\arctan x$ 로 두면 $\\int u^{2}du$ 다.', '거듭제곱 법칙으로 끝난다.'],
  steps: ['$u=\\arctan x$', '$\\dfrac{\\arctan^{3}x}{3}$']
});
add('hard', '쌍곡선 고차', 'tanh(x)^5', 'ln(cosh(x))-tanh(x)^2/2-tanh(x)^4/4', {
  domain: D.hypP,
  hints: ['$\\tanh^{5}=\\tanh^{3}(1-\\operatorname{sech}^{2})$ 로 내린다.',
          '$\\int\\tanh^{3}=\\ln\\cosh x-\\dfrac{\\tanh^{2}}{2}$'],
  steps: ['$\\int\\tanh^{5}=\\int\\tanh^{3}-\\dfrac{\\tanh^{4}}{4}$',
          '$=\\ln\\cosh x-\\dfrac{\\tanh^{2}x}{2}-\\dfrac{\\tanh^{4}x}{4}$']
});
add('hard', '쌍곡선 부분적분', 'x*sech(x)^2', 'x*tanh(x)-ln(cosh(x))', {
  domain: D.hypP,
  hints: ['$dv=\\operatorname{sech}^{2}x\\,dx\\Rightarrow v=\\tanh x$', '$\\int\\tanh x\\,dx=\\ln\\cosh x$'],
  steps: ['$=x\\tanh x-\\int\\tanh x\\,dx$', '$=x\\tanh x-\\ln\\cosh x$']
});
add('hard', '역쌍곡선 부분적분', 'x^2*atanh(x)', 'x^3*atanh(x)/3+ln(1-x^2)/6+x^2/6', {
  domain: D.unit,
  hints: ['$v=\\dfrac{x^{3}}{3}$ 로 부분적분하면 $\\dfrac13\\int\\dfrac{x^{3}}{1-x^{2}}dx$ 가 남는다.',
          '$\\dfrac{x^{3}}{1-x^{2}}=-x+\\dfrac{x}{1-x^{2}}$'],
  steps: ['$=\\dfrac{x^{3}\\operatorname{artanh}x}{3}-\\dfrac13\\int\\dfrac{x^{3}}{1-x^{2}}dx$',
          '$=\\dfrac{x^{3}\\operatorname{artanh}x}{3}+\\dfrac{\\ln(1-x^{2})}{6}+\\dfrac{x^{2}}{6}$']
});
add('hard', '미분 꼴 알아보기', 'e^(-x)*(x+1)/x^2', '-e^(-x)/x', {
  domain: D.pos,
  hints: ['$\\left(\\dfrac{e^{-x}}{x}\\right)\'$ 를 계산해 본다.',
          '$=-\\dfrac{e^{-x}}{x}-\\dfrac{e^{-x}}{x^{2}}=-\\dfrac{e^{-x}(x+1)}{x^{2}}$'],
  steps: ['몫의 미분법을 거꾸로 읽는다', '$=-\\dfrac{e^{-x}}{x}$']
});
add('hard', '로그 미분법', 'ln(1+1/x)', 'x*ln(1+1/x)+ln(1+x)', {
  domain: D.pos,
  hints: ['$dv=dx$ 로 부분적분한다.',
          '$\\left(\\ln\\left(1+\\dfrac1x\\right)\\right)\'=-\\dfrac{1}{x(x+1)}$'],
  steps: ['$=x\\ln\\left(1+\\dfrac1x\\right)+\\int\\dfrac{dx}{x+1}$',
          '$=x\\ln\\left(1+\\dfrac1x\\right)+\\ln(1+x)$']
});

// ================================================================== 몬스터 보강
// 치환을 스스로 찾아내야 하거나, 겉모습이 답을 전혀 알려주지 않는 것들.

add('monster', '괴상한 지수', '1/(x^4+1)^(5/4)', 'x/(x^4+1)^(1/4)', {
  domain: [0.2, 2.6],
  hints: ['$\\dfrac{x}{(x^{4}+1)^{1/4}}$ 를 미분해 본다.',
          '분자에서 $(x^{4}+1)-x^{4}=1$ 이 남아 지수가 $-\\dfrac54$ 로 정확히 맞는다.'],
  steps: ['$F=\\dfrac{x}{(x^{4}+1)^{1/4}}$',
          '$F\'=\\dfrac{(x^{4}+1)-x^{4}}{(x^{4}+1)^{5/4}}=\\dfrac{1}{(x^{4}+1)^{5/4}}$',
          '일반적으로 $\\int\\dfrac{dx}{(x^{n}+1)^{(n+1)/n}}=\\dfrac{x}{(x^{n}+1)^{1/n}}$']
});
add('monster', '괴상한 지수', '1/(x^3+1)^(4/3)', 'x/(x^3+1)^(1/3)', {
  domain: [0.2, 2.6],
  hints: ['앞 문제와 같은 꼴 — $n=3$ 이다.', '$\\dfrac{x}{(x^{3}+1)^{1/3}}$ 를 미분해 확인한다.'],
  steps: ['$F=\\dfrac{x}{(x^{3}+1)^{1/3}}$',
          '$F\'=\\dfrac{(x^{3}+1)-x^{3}}{(x^{3}+1)^{4/3}}=\\dfrac{1}{(x^{3}+1)^{4/3}}$']
});
add('monster', '괴상한 지수', '1/(1-x^4)^(5/4)', 'x/(1-x^4)^(1/4)', {
  domain: D.unit,
  hints: ['부호만 바뀐 같은 구조다.', '$\\dfrac{x}{(1-x^{4})^{1/4}}$ 를 미분해 본다.'],
  steps: ['$F\'=\\dfrac{(1-x^{4})+x^{4}}{(1-x^{4})^{5/4}}=\\dfrac{1}{(1-x^{4})^{5/4}}$']
});
add('monster', '중첩 근호', 'sqrt(x+sqrt(x^2-1))', 'sqrt(2)*((x+1)^(3/2)+(x-1)^(3/2))/3', {
  domain: [1.3, 3.4],
  hints: ['$\\left(\\dfrac{\\sqrt{x+1}+\\sqrt{x-1}}{\\sqrt2}\\right)^{2}=x+\\sqrt{x^{2}-1}$ 임을 확인한다.',
          '중첩 근호가 풀리면 거듭제곱 적분 두 개만 남는다.'],
  steps: ['$\\sqrt{x+\\sqrt{x^{2}-1}}=\\dfrac{\\sqrt{x+1}+\\sqrt{x-1}}{\\sqrt2}$',
          '$\\dfrac{1}{\\sqrt2}\\left[\\dfrac{2(x+1)^{3/2}}{3}+\\dfrac{2(x-1)^{3/2}}{3}\\right]$']
});
add('monster', '역수 치환', '(x^2-1)/((x^2+1)*sqrt(x^4+3*x^2+1))',
    'ln((x^2+1)/(x+sqrt(x^4+3*x^2+1)))', {
  domain: [0.3, 2.6], lnAbs: true,
  hints: ['분자·분모를 $x^{2}$ 로 나눈다. $u=x+\\dfrac1x$ 로 두면 $x^{2}+3+\\dfrac{1}{x^{2}}=u^{2}+1$ 이다.',
          '$\\int\\dfrac{du}{u\\sqrt{u^{2}+1}}=\\ln\\left|\\dfrac{u}{1+\\sqrt{u^{2}+1}}\\right|$'],
  steps: ['$u=x+\\dfrac1x,\;du=\\left(1-\\dfrac{1}{x^{2}}\\right)dx$',
          '$\\sqrt{u^{2}+1}=\\dfrac{\\sqrt{x^{4}+3x^{2}+1}}{x}$',
          '되돌리면 $\\ln\\dfrac{x^{2}+1}{x+\\sqrt{x^{4}+3x^{2}+1}}$']
});
add('monster', '역수 치환', '(x^2+1)/((x^2-1)*sqrt(x^4+1))',
    'ln((x^2-1)/(sqrt(2)*x+sqrt(x^4+1)))/sqrt(2)', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['이번엔 $u=x-\\dfrac1x$ 로 두면 $x^{2}+\\dfrac{1}{x^{2}}=u^{2}+2$ 다.',
          '$\\int\\dfrac{du}{u\\sqrt{u^{2}+2}}=\\dfrac{1}{\\sqrt2}\\ln\\left|\\dfrac{u}{\\sqrt2+\\sqrt{u^{2}+2}}\\right|$'],
  steps: ['$u=x-\\dfrac1x,\;du=\\left(1+\\dfrac{1}{x^{2}}\\right)dx$',
          '$\\sqrt{u^{2}+2}=\\dfrac{\\sqrt{x^{4}+1}}{x}$',
          '$=\\dfrac{1}{\\sqrt2}\\ln\\dfrac{x^{2}-1}{\\sqrt2\\,x+\\sqrt{x^{4}+1}}$']
});
add('monster', '8차 유리식', '1/(1+x^2+x^4+x^6)',
    'arctan(x)/2-ln((x^2-sqrt(2)*x+1)/(x^2+sqrt(2)*x+1))/(4*sqrt(2))', {
  domain: [0.2, 2.6],
  hints: ['분모는 등비수열의 합 $\\dfrac{x^{8}-1}{x^{2}-1}=(1+x^{2})(1+x^{4})$ 다.',
          '$\\dfrac{1}{(1+x^{2})(1+x^{4})}=\\dfrac{1}{2(1+x^{2})}+\\dfrac{1-x^{2}}{2(1+x^{4})}$'],
  steps: ['$1+x^{2}+x^{4}+x^{6}=(1+x^{2})(1+x^{4})$ 로 묶는다',
          '$\\int\\dfrac{x^{2}-1}{x^{4}+1}dx=\\dfrac{1}{2\\sqrt2}\\ln\\dfrac{x^{2}-\\sqrt2x+1}{x^{2}+\\sqrt2x+1}$ 를 쓴다']
});
add('monster', '삼각 6차', '1/(sin(x)^6+cos(x)^6)', 'arctan(tan(2*x)/2)', {
  domain: [0.08, 0.68],
  hints: ['$\\sin^{6}+\\cos^{6}=1-3\\sin^{2}\\cos^{2}=1-\\dfrac34\\sin^{2}2x$ 로 줄인다.',
          '$u=\\tan 2x$ 로 두면 $\\int\\dfrac{du}{4+u^{2}}\\cdot 2$ 가 된다.'],
  steps: ['$\\sin^{6}x+\\cos^{6}x=1-\\dfrac{3}{4}\\sin^{2}2x$',
          '$u=\\tan 2x$ 로 두면 분모가 $4+u^{2}$ 로 정리된다',
          '$=\\arctan\\dfrac{\\tan 2x}{2}$']
});
add('monster', '몫의 미분 되짚기', 'x^2/(x*sin(x)+cos(x))^2',
    '(sin(x)-x*cos(x))/(x*sin(x)+cos(x))', {
  domain: [0.2, 1.3],
  hints: ['$(x\\sin x+\\cos x)\'=x\\cos x$ 라는 점이 열쇠다.',
          '$\\dfrac{\\sin x-x\\cos x}{x\\sin x+\\cos x}$ 를 미분해 본다.'],
  steps: ['$N=\\sin x-x\\cos x,\;N\'=x\\sin x$',
          '$D=x\\sin x+\\cos x,\;D\'=x\\cos x$',
          '$N\'D-ND\'=x^{2}(\\sin^{2}x+\\cos^{2}x)=x^{2}$']
});
add('monster', '역삼각 치환', 'e^(arctan(x))/(1+x^2)^(3/2)',
    'e^(arctan(x))*(x+1)/(2*sqrt(1+x^2))', {
  domain: [0.2, 2.4],
  hints: ['$t=\\arctan x$ 로 두면 $dx=\\sec^{2}t\\,dt$, $(1+x^{2})^{3/2}=\\sec^{3}t$ 다.',
          '$\\int e^{t}\\cos t\\,dt=\\dfrac{e^{t}(\\sin t+\\cos t)}{2}$'],
  steps: ['$t=\\arctan x$ 로 두면 $\\int e^{t}\\cos t\\,dt$',
          '$\\sin t=\\dfrac{x}{\\sqrt{1+x^{2}}},\;\\cos t=\\dfrac{1}{\\sqrt{1+x^{2}}}$',
          '$=\\dfrac{e^{\\arctan x}(x+1)}{2\\sqrt{1+x^{2}}}$']
});
add('monster', '역삼각 치환', 'x*e^(arctan(x))/(1+x^2)^(3/2)',
    'e^(arctan(x))*(x-1)/(2*sqrt(1+x^2))', {
  domain: [0.2, 2.4],
  hints: ['같은 치환에서 이번엔 $\\int e^{t}\\sin t\\,dt$ 가 된다.',
          '$\\int e^{t}\\sin t\\,dt=\\dfrac{e^{t}(\\sin t-\\cos t)}{2}$'],
  steps: ['$t=\\arctan x$', '$\\dfrac{e^{\\arctan x}(x-1)}{2\\sqrt{1+x^{2}}}$']
});
add('monster', '몫의 미분 되짚기', 'ln(x)/(1+ln(x))^2', 'x/(1+ln(x))', {
  domain: [1.2, 4.0],
  hints: ['$\\dfrac{x}{1+\\ln x}$ 를 미분해 본다. 분모에 $x$ 가 없다는 점에 주의.',
          '$\\left(\\dfrac{x}{1+\\ln x}\\right)\'=\\dfrac{(1+\\ln x)-1}{(1+\\ln x)^{2}}$'],
  steps: ['몫의 미분법을 거꾸로 읽는다',
          '$=\\dfrac{\\ln x}{(1+\\ln x)^{2}}$ 이므로 원시함수는 $\\dfrac{x}{1+\\ln x}$']
});
add('monster', '몫의 미분 되짚기', '(ln(x)-2)/ln(x)^3', 'x/ln(x)^2', {
  domain: [1.6, 4.6],
  hints: ['$\\dfrac{x}{\\ln^{2}x}$ 를 미분해 본다.',
          '$\\left(\\dfrac{x}{\\ln^{2}x}\\right)\'=\\dfrac{\\ln^{2}x-2\\ln x}{\\ln^{4}x}$'],
  steps: ['$\\dfrac{\\ln^{2}x-2\\ln x}{\\ln^{4}x}=\\dfrac{\\ln x-2}{\\ln^{3}x}$',
          '따라서 원시함수는 $\\dfrac{x}{\\ln^{2}x}$']
});
add('monster', '곱의 미분 되짚기', '(1+3*x^3)*e^(x^3)', 'x*e^(x^3)', {
  domain: [0.2, 1.3],
  hints: ['$\\left(xe^{x^{3}}\\right)\'$ 를 계산해 본다.', '$=e^{x^{3}}+3x^{3}e^{x^{3}}$'],
  steps: ['$\\left(xe^{x^{3}}\\right)\'=e^{x^{3}}(1+3x^{3})$', '따라서 원시함수는 $xe^{x^{3}}$']
});
add('monster', '함정 문제', 'sqrt((x-1)/(x^3-x^2))', 'ln(x)', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['분모를 인수분해해 보자: $x^{3}-x^{2}=x^{2}(x-1)$.',
          '약분하면 근호 안이 $\\dfrac{1}{x^{2}}$ 만 남는다.'],
  steps: ['$\\dfrac{x-1}{x^{2}(x-1)}=\\dfrac{1}{x^{2}}$',
          '피적분함수는 $\\dfrac1x$', '$\\int\\dfrac{dx}{x}=\\ln|x|$']
});
add('monster', '지수 근호', 'sqrt(1+e^x)',
    '2*sqrt(1+e^x)+ln((sqrt(1+e^x)-1)/(sqrt(1+e^x)+1))', {
  domain: [0.2, 2.0], lnAbs: true,
  hints: ['$u=\\sqrt{1+e^{x}}$ 로 두면 $dx=\\dfrac{2u\\,du}{u^{2}-1}$ 다.',
          '$\\dfrac{2u^{2}}{u^{2}-1}=2+\\dfrac{2}{u^{2}-1}$'],
  steps: ['$u=\\sqrt{1+e^{x}}$',
          '$\\int\\left(2+\\dfrac{2}{u^{2}-1}\\right)du=2u+\\ln\\left|\\dfrac{u-1}{u+1}\\right|$']
});
add('monster', '삼각 유리식', 'sin(x)^2/(1+sin(x)^2)', 'x-atan(sqrt(2)*tan(x))/sqrt(2)', {
  domain: D.trig,
  hints: ['$\\dfrac{\\sin^{2}}{1+\\sin^{2}}=1-\\dfrac{1}{1+\\sin^{2}}$ 로 쪼갠다.',
          '$\\int\\dfrac{dx}{1+\\sin^{2}x}=\\dfrac{1}{\\sqrt2}\\arctan(\\sqrt2\\tan x)$'],
  steps: ['$1-\\dfrac{1}{1+\\sin^{2}x}$ 로 나눈다',
          '$=x-\\dfrac{1}{\\sqrt2}\\arctan(\\sqrt2\\tan x)$']
});
add('monster', '로그 치환', 'ln(x)^2/(x*sqrt(1+ln(x)^3))', '2*sqrt(1+ln(x)^3)/3', {
  domain: [1.2, 4.0],
  hints: ['$u=1+\\ln^{3}x$ 로 두면 $du=\\dfrac{3\\ln^{2}x}{x}dx$ 다.', '$\\dfrac13\\int u^{-1/2}du$'],
  steps: ['$u=1+\\ln^{3}x$', '$\\dfrac13\\cdot 2\\sqrt u=\\dfrac{2\\sqrt{1+\\ln^{3}x}}{3}$']
});
add('monster', '복합 부분적분', 'arctan(x)/(x^2*(1+x^2))',
    'ln(x)-ln(1+x^2)/2-arctan(x)/x-arctan(x)^2/2', {
  domain: [0.25, 2.4], lnAbs: true,
  hints: ['$\\dfrac{1}{x^{2}(1+x^{2})}=\\dfrac{1}{x^{2}}-\\dfrac{1}{1+x^{2}}$ 로 먼저 쪼갠다.',
          '$\\int\\dfrac{\\arctan x}{x^{2}}dx$ 와 $\\int\\dfrac{\\arctan x}{1+x^{2}}dx$ 를 각각 계산한다.'],
  steps: ['$\\int\\dfrac{\\arctan x}{x^{2}}dx=\\ln|x|-\\dfrac{\\ln(1+x^{2})}{2}-\\dfrac{\\arctan x}{x}$',
          '$\\int\\dfrac{\\arctan x}{1+x^{2}}dx=\\dfrac{\\arctan^{2}x}{2}$',
          '두 결과를 뺀다']
});
add('monster', '유리식 치환', '1/(x*sqrt(x^4-1))', 'arctan(sqrt(x^4-1))/2', {
  domain: [1.3, 3.0],
  hints: ['분자·분모에 $x^{3}$ 을 곱해 $u=x^{4}$ 를 만든다.',
          '$s=\\sqrt{u-1}$ 로 다시 치환하면 $\\int\\dfrac{ds}{s^{2}+1}$ 이다.'],
  steps: ['$u=x^{4}:\;\\dfrac14\\int\\dfrac{du}{u\\sqrt{u-1}}$',
          '$s=\\sqrt{u-1}:\;\\dfrac12\\int\\dfrac{ds}{s^{2}+1}$',
          '$=\\dfrac{\\arctan\\sqrt{x^{4}-1}}{2}$']
});

// ================================================================== 연습 세트 보강
// 일반적인 미적분 연습 문제집이 다루는 기본기 — u-치환, 부분적분, 삼각적분,
// 삼각치환, 부분분수 — 에서 아직 비어 있던 자리를 채운다.

// --- 쉬움: 눈에 보이는 u-치환
add('easy', '치환적분', 'x/sqrt(1-x^2)', '-sqrt(1-x^2)', {
  domain: D.unit,
  hints: ['$u=1-x^{2}$ 로 두면 $du=-2x\\,dx$ 다.', '$-\\dfrac12\\int u^{-1/2}du$'],
  steps: ['$u=1-x^{2}$', '$-\\dfrac12\\cdot 2\\sqrt u=-\\sqrt{1-x^{2}}$']
});
add('easy', '치환적분', 'sin(x)^3*cos(x)', 'sin(x)^4/4', {
  domain: D.trigW,
  hints: ['$u=\\sin x$ 로 두면 $du=\\cos x\\,dx$ 다.', '$\\int u^{3}du$ 만 남는다.'],
  steps: ['$u=\\sin x$', '$\\dfrac{\\sin^{4}x}{4}$']
});
add('easy', '치환적분', 'x*cos(x^2)', 'sin(x^2)/2', {
  domain: [0.2, 1.5],
  hints: ['$u=x^{2}$ 로 두면 $du=2x\\,dx$ 다.', '$\\dfrac12\\int\\cos u\\,du$'],
  steps: ['$u=x^{2}$', '$\\dfrac{\\sin(x^{2})}{2}$']
});
add('easy', '치환적분', 'e^x*cos(e^x)', 'sin(e^x)', {
  domain: [-1.0, 1.0],
  hints: ['$u=e^{x}$ 로 두면 $du=e^{x}dx$ 다.', '$\\int\\cos u\\,du=\\sin u$'],
  steps: ['$u=e^{x}$', '$\\sin(e^{x})$']
});
add('easy', '치환적분', 'cos(x)/(1+sin(x))', 'ln(1+sin(x))', {
  domain: D.trigW,
  hints: ['분모의 미분이 분자에 그대로 있다.', '$\\int\\dfrac{f\'}{f}dx=\\ln|f|$'],
  steps: ['$u=1+\\sin x$', '$\\ln(1+\\sin x)$']
});
add('easy', '치환적분', 'sec(x)^2*e^(tan(x))', 'e^(tan(x))', {
  domain: D.trig,
  hints: ['$u=\\tan x$ 로 두면 $du=\\sec^{2}x\\,dx$ 다.', '$\\int e^{u}du=e^{u}$'],
  steps: ['$u=\\tan x$', '$e^{\\tan x}$']
});
add('easy', '치환적분', 'e^(1/x)/x^2', '-e^(1/x)', {
  domain: [0.5, 2.6],
  hints: ['$u=\\dfrac1x$ 로 두면 $du=-\\dfrac{dx}{x^{2}}$ 다.', '$-\\int e^{u}du$'],
  steps: ['$u=\\dfrac1x$', '$-e^{1/x}$']
});
add('easy', '치환적분', 'cos(1/x)/x^2', '-sin(1/x)', {
  domain: [0.4, 2.6],
  hints: ['$u=\\dfrac1x$ 로 두면 $du=-\\dfrac{dx}{x^{2}}$ 다.', '$-\\int\\cos u\\,du$'],
  steps: ['$u=\\dfrac1x$', '$-\\sin\\dfrac1x$']
});
add('easy', '거듭제곱 법칙', '(x+1)/sqrt(x)', '2*x^(3/2)/3+2*sqrt(x)', {
  domain: D.pos,
  hints: ['분모로 나눠 $x^{1/2}+x^{-1/2}$ 로 먼저 편다.', '각각 거듭제곱 법칙을 쓴다.'],
  steps: ['$\\dfrac{x+1}{\\sqrt x}=\\sqrt x+\\dfrac{1}{\\sqrt x}$',
          '$=\\dfrac{2x^{3/2}}{3}+2\\sqrt x$']
});
add('easy', '치환적분', 'sin(x)/cos(x)^3', '1/(2*cos(x)^2)', {
  domain: D.trig,
  hints: ['$u=\\cos x$ 로 두면 $du=-\\sin x\\,dx$ 다.', '$-\\int u^{-3}du=\\dfrac{1}{2u^{2}}$'],
  steps: ['$u=\\cos x$', '$\\dfrac{1}{2\\cos^{2}x}$']
});

// --- 보통: 한 번 손보고 나서 표준 기법
add('medium', '치환적분', 'tan(x)*sec(x)^3', 'sec(x)^3/3', {
  domain: D.trig,
  hints: ['$\\sec^{3}\\tan=\\sec^{2}\\cdot(\\sec\\tan)$ 로 갈라 본다.',
          '$u=\\sec x,\;du=\\sec x\\tan x\\,dx$'],
  steps: ['$u=\\sec x$', '$\\int u^{2}du=\\dfrac{\\sec^{3}x}{3}$']
});
add('medium', '치환적분', 'arcsin(x)^3/sqrt(1-x^2)', 'arcsin(x)^4/4', {
  domain: D.unit,
  hints: ['$u=\\arcsin x$ 로 두면 $du=\\dfrac{dx}{\\sqrt{1-x^{2}}}$ 다.', '$\\int u^{3}du$'],
  steps: ['$u=\\arcsin x$', '$\\dfrac{\\arcsin^{4}x}{4}$']
});
add('medium', '치환적분', 'sinh(x)/(1+cosh(x))', 'ln(1+cosh(x))', {
  domain: D.hyp,
  hints: ['분모의 미분이 분자다.', '$\\int\\dfrac{f\'}{f}dx=\\ln|f|$'],
  steps: ['$u=1+\\cosh x$', '$\\ln(1+\\cosh x)$']
});
add('medium', '부분적분', 'ln(2*x+1)', '(2*x+1)*ln(2*x+1)/2-x', {
  domain: [0.2, 2.4],
  hints: ['$v=\\dfrac{2x+1}{2}$ 로 잡으면 남는 적분이 $\\int dx$ 로 줄어든다.',
          '$\\int\\ln(ax+b)dx=\\dfrac{(ax+b)\\ln(ax+b)-(ax+b)}{a}$'],
  steps: ['$v=\\dfrac{2x+1}{2}$ 로 부분적분',
          '$=\\dfrac{(2x+1)\\ln(2x+1)}{2}-x$']
});
add('medium', '치환적분', 'x*sqrt(1+x)', '2*(1+x)^(5/2)/5-2*(1+x)^(3/2)/3', {
  domain: [0.2, 3.0],
  hints: ['$u=1+x$ 로 두고 $x=u-1$ 을 대입한다.', '$\\int(u-1)\\sqrt u\\,du$ 로 펴진다.'],
  steps: ['$u=1+x$', '$\\int(u^{3/2}-u^{1/2})du=\\dfrac{2u^{5/2}}{5}-\\dfrac{2u^{3/2}}{3}$']
});
add('medium', '삼각 항등식', '1/(sin(x)^2*cos(x)^2)', 'tan(x)-cot(x)', {
  domain: [0.35, 1.2],
  hints: ['분자에 $\\sin^{2}x+\\cos^{2}x=1$ 을 끼워 넣는다.',
          '$\\dfrac{1}{\\sin^{2}\\cos^{2}}=\\sec^{2}x+\\csc^{2}x$'],
  steps: ['$\\sec^{2}x+\\csc^{2}x$ 로 나눈다', '$=\\tan x-\\cot x$']
});
add('medium', '삼각함수 고차', 'tan(x)^2*sec(x)^4', 'tan(x)^3/3+tan(x)^5/5', {
  domain: D.trig,
  hints: ['$\\sec^{4}=\\sec^{2}(1+\\tan^{2})$ 로 하나를 떼어낸다.', '$u=\\tan x$ 로 치환한다.'],
  steps: ['$u=\\tan x$', '$\\int u^{2}(1+u^{2})du=\\dfrac{u^{3}}{3}+\\dfrac{u^{5}}{5}$']
});
add('medium', '삼각치환', '1/sqrt(4-9*x^2)', 'arcsin(3*x/2)/3', {
  domain: [-0.5, 0.5],
  hints: ['$\\sqrt{4-9x^{2}}=2\\sqrt{1-(3x/2)^{2}}$ 로 정리한다.',
          '$\\int\\dfrac{du}{\\sqrt{1-u^{2}}}=\\arcsin u$'],
  steps: ['$u=\\dfrac{3x}{2},\;du=\\dfrac32dx$', '$\\dfrac13\\arcsin\\dfrac{3x}{2}$']
});
add('medium', '삼각치환', 'sqrt(9-4*x^2)', 'x*sqrt(9-4*x^2)/2+9*arcsin(2*x/3)/4', {
  domain: [-1.0, 1.0],
  hints: ['$u=2x$ 로 두면 $\\dfrac12\\int\\sqrt{9-u^{2}}du$ 다.',
          '$\\int\\sqrt{a^{2}-u^{2}}du=\\dfrac{u\\sqrt{a^{2}-u^{2}}}{2}+\\dfrac{a^{2}}{2}\\arcsin\\dfrac ua$'],
  steps: ['$u=2x,\;a=3$', '$=\\dfrac{x\\sqrt{9-4x^{2}}}{2}+\\dfrac94\\arcsin\\dfrac{2x}{3}$']
});
add('medium', '부분분수', '(3*x+5)/((x-1)*(x+2))', '8*ln(x-1)/3+ln(x+2)/3', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['가리기(cover-up)로 $x=1$ 과 $x=-2$ 를 대입한다.', '계수는 $\\dfrac83$ 과 $\\dfrac13$ 이다.'],
  steps: ['$\\dfrac{8/3}{x-1}+\\dfrac{1/3}{x+2}$', '각 항을 로그로 적분']
});
add('medium', '부분분수', '1/(x^3-x)', 'ln(x^2-1)/2-ln(x)', {
  domain: [1.4, 3.4], lnAbs: true,
  hints: ['$x^{3}-x=x(x-1)(x+1)$ 로 인수분해한다.', '계수는 $-1,\;\\dfrac12,\;\\dfrac12$ 다.'],
  steps: ['$-\\dfrac1x+\\dfrac{1/2}{x-1}+\\dfrac{1/2}{x+1}$',
          '$=\\dfrac{\\ln|x^{2}-1|}{2}-\\ln|x|$']
});
add('medium', '부분분수', '1/(x^2+2*x)', 'ln(x/(x+2))/2', {
  domain: D.pos, lnAbs: true,
  hints: ['$x^{2}+2x=x(x+2)$ 로 묶는다.',
          '$\\dfrac{1}{x(x+2)}=\\dfrac12\\left(\\dfrac1x-\\dfrac{1}{x+2}\\right)$'],
  steps: ['부분분수로 쪼갠다', '$=\\dfrac12\\ln\\left|\\dfrac{x}{x+2}\\right|$']
});
add('medium', '지수 항등식', '(e^x-e^(-x))/(e^x+e^(-x))', 'ln(cosh(x))', {
  domain: [-1.5, 1.7],
  hints: ['피적분함수는 $\\tanh x$ 다.', '분모의 미분이 분자이므로 로그가 된다.'],
  steps: ['$\\dfrac{e^{x}-e^{-x}}{e^{x}+e^{-x}}=\\tanh x$', '$\\int\\tanh x\\,dx=\\ln\\cosh x$']
});
add('medium', '치환적분', 'sec(x)^2/(1+tan(x))', 'ln(1+tan(x))', {
  domain: D.trig, lnAbs: true,
  hints: ['$u=1+\\tan x$ 로 두면 $du=\\sec^{2}x\\,dx$ 다.', '$\\int\\dfrac{du}{u}=\\ln|u|$'],
  steps: ['$u=1+\\tan x$', '$\\ln|1+\\tan x|$']
});
add('medium', '완전제곱', 'x/(x^2+2*x+2)', 'ln(x^2+2*x+2)/2-arctan(x+1)', {
  domain: [0.2, 2.6],
  hints: ['분자를 $\\dfrac{(2x+2)}{2}-1$ 로 쪼갠다.', '$x^{2}+2x+2=(x+1)^{2}+1$'],
  steps: ['$\\dfrac12\\int\\dfrac{2x+2}{x^{2}+2x+2}dx=\\dfrac{\\ln(x^{2}+2x+2)}{2}$',
          '$-\\int\\dfrac{dx}{(x+1)^{2}+1}=-\\arctan(x+1)$']
});
add('medium', '로그 치환', '1/(x*(1-ln(x)))', '-ln(1-ln(x))', {
  domain: [1.2, 2.4], lnAbs: true,
  hints: ['$u=1-\\ln x$ 로 두면 $du=-\\dfrac{dx}{x}$ 다.', '$-\\int\\dfrac{du}{u}$'],
  steps: ['$u=1-\\ln x$', '$-\\ln|1-\\ln x|$']
});
add('medium', '치환적분', 'sin(2*x)/(1+cos(x)^2)', '-ln(1+cos(x)^2)', {
  domain: D.trigW,
  hints: ['$\\sin 2x=2\\sin x\\cos x$ 이므로 $u=1+\\cos^{2}x$ 의 미분이 보인다.',
          '$du=-2\\sin x\\cos x\\,dx=-\\sin 2x\\,dx$'],
  steps: ['$u=1+\\cos^{2}x$', '$-\\ln(1+\\cos^{2}x)$']
});
add('medium', '유리화 치환', '1/(1+sqrt(2*x))', 'sqrt(2*x)-ln(1+sqrt(2*x))', {
  domain: D.pos,
  hints: ['$u=\\sqrt{2x}$ 로 두면 $dx=u\\,du$ 다.',
          '$\\dfrac{u}{1+u}=1-\\dfrac{1}{1+u}$'],
  steps: ['$u=\\sqrt{2x}$', '$\\int\\left(1-\\dfrac{1}{1+u}\\right)du=u-\\ln(1+u)$']
});
add('medium', '치환적분', 'tan(x)*ln(cos(x))', '-ln(cos(x))^2/2', {
  domain: D.trig, lnAbs: true,
  hints: ['$u=\\ln\\cos x$ 로 두면 $du=-\\tan x\\,dx$ 다.', '$-\\int u\\,du$'],
  steps: ['$u=\\ln\\cos x$', '$-\\dfrac{\\ln^{2}\\cos x}{2}$']
});
add('medium', '치환+부분분수', 'x/(1-x^4)', 'ln((1+x^2)/(1-x^2))/4', {
  domain: D.unit, lnAbs: true,
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\int\\dfrac{du}{1-u^{2}}$ 다.',
          '$\\int\\dfrac{du}{1-u^{2}}=\\dfrac12\\ln\\left|\\dfrac{1+u}{1-u}\\right|$'],
  steps: ['$u=x^{2}$', '$\\dfrac14\\ln\\left|\\dfrac{1+x^{2}}{1-x^{2}}\\right|$']
});

// ================================================================== 올림피아드 연습 세트
// 문제식은 "300 Integral Practice Set" (Maths Olympiad Preparation, 2024) 에서 골랐고,
// 기준 부정적분은 여기서 다시 유도해 수치 검증을 통과시킨 것이다.

// --- 쉬움/보통
add('easy', '치환적분', '6*x^2*sin(x^3+1)', '-2*cos(x^3+1)', {
  domain: [0.2, 1.5],
  hints: ['$u=x^{3}+1$ 로 두면 $du=3x^{2}dx$ 다.', '$2\\int\\sin u\\,du$ 만 남는다.'],
  steps: ['$u=x^{3}+1$', '$-2\\cos(x^{3}+1)$']
});
add('medium', '치환적분', 'x*sqrt(x+2)', '2*(3*x-4)*(x+2)^(3/2)/15', {
  domain: [0.2, 3.0],
  hints: ['$u=x+2$ 로 두고 $x=u-2$ 를 대입한다.', '$\\int(u^{3/2}-2u^{1/2})du$ 로 펴진다.'],
  steps: ['$u=x+2$', '$\\dfrac{2u^{5/2}}{5}-\\dfrac{4u^{3/2}}{3}=\\dfrac{2(3x-4)(x+2)^{3/2}}{15}$']
});
add('medium', '치환적분', 'x*(1+x)^(1/5)', '5*(6*x-5)*(1+x)^(6/5)/66', {
  domain: [0.2, 3.0],
  hints: ['$u=1+x$ 로 두고 $x=u-1$ 을 대입한다.', '$\\int(u^{6/5}-u^{1/5})du$'],
  steps: ['$u=1+x$', '$\\dfrac{5u^{11/5}}{11}-\\dfrac{5u^{6/5}}{6}=\\dfrac{5(6x-5)(1+x)^{6/5}}{66}$']
});
add('medium', '삼각함수 고차', 'tan(x)^4*sec(x)^6', 'tan(x)^9/9+2*tan(x)^7/7+tan(x)^5/5', {
  domain: D.trig,
  hints: ['$\\sec^{6}=\\sec^{2}(1+\\tan^{2})^{2}$ 로 하나를 떼어낸다.', '$u=\\tan x$ 로 치환해 전개한다.'],
  steps: ['$u=\\tan x$', '$\\int u^{4}(1+u^{2})^{2}du=\\dfrac{u^{9}}{9}+\\dfrac{2u^{7}}{7}+\\dfrac{u^{5}}{5}$']
});
add('medium', '삼각함수 홀수차', 'sin(x)^3/cos(x)^8', '1/(7*cos(x)^7)-1/(5*cos(x)^5)', {
  domain: D.trig,
  hints: ['$\\sin^{3}=\\sin x(1-\\cos^{2}x)$ 로 하나를 떼어낸다.', '$u=\\cos x$ 로 두면 $-\\int(u^{-8}-u^{-6})du$'],
  steps: ['$u=\\cos x$', '$\\dfrac{1}{7\\cos^{7}x}-\\dfrac{1}{5\\cos^{5}x}$']
});

// --- 어려움
add('hard', '유리식 정리', '(2*x^3-1)/(x*(x^3+1))', 'ln((x^3+1)/x)', {
  domain: D.pos, lnAbs: true,
  hints: ['답을 $\\ln\\left|\\dfrac{x^{3}+1}{x}\\right|$ 로 놓고 미분해 본다.',
          '$\\dfrac{3x^{2}}{x^{3}+1}-\\dfrac1x$ 를 통분하면 분자가 $2x^{3}-1$ 이다.'],
  steps: ['$\\dfrac{3x^{2}}{x^{3}+1}-\\dfrac1x=\\dfrac{3x^{3}-(x^{3}+1)}{x(x^{3}+1)}$',
          '$=\\dfrac{2x^{3}-1}{x(x^{3}+1)}$']
});
add('hard', '삼각 유리식', 'sin(x)/(cos(x)^3+sin(x)*cos(x)^2)', 'tan(x)-ln(1+tan(x))', {
  domain: D.trig, lnAbs: true,
  hints: ['분모를 $\\cos^{2}x(\\cos x+\\sin x)$ 로 묶고 분자·분모를 $\\cos^{3}x$ 로 나눈다.',
          '$\\dfrac{\\tan x\\sec^{2}x}{1+\\tan x}$ 가 되어 $u=\\tan x$ 치환이 통한다.'],
  steps: ['$u=\\tan x$ 로 두면 $\\int\\dfrac{u}{1+u}du$',
          '$=u-\\ln|1+u|=\\tan x-\\ln|1+\\tan x|$']
});
add('hard', '로그 치환', '(ln(x)-ln(x+1))/(x*(x+1))', 'ln(1+1/x)^2/2', {
  domain: D.pos,
  hints: ['$u=\\ln\\dfrac{x+1}{x}=\\ln\\left(1+\\dfrac1x\\right)$ 로 둔다.',
          '$du=-\\dfrac{dx}{x(x+1)}$ 이고 분자는 $-u$ 다.'],
  steps: ['$u=\\ln\\left(1+\\dfrac1x\\right),\;du=-\\dfrac{dx}{x(x+1)}$',
          '$\\int u\\,du=\\dfrac{u^{2}}{2}$']
});
add('hard', '부분적분', 'arctan(x)/x^4', 'ln((1+x^2)/x^2)/6-arctan(x)/(3*x^3)-1/(6*x^2)', {
  domain: D.pos,
  hints: ['$v=-\\dfrac{1}{3x^{3}}$ 로 부분적분한다.',
          '남는 $\\int\\dfrac{dx}{3x^{3}(1+x^{2})}$ 를 부분분수로 쪼갠다.'],
  steps: ['$=-\\dfrac{\\arctan x}{3x^{3}}+\\dfrac13\\int\\dfrac{dx}{x^{3}(1+x^{2})}$',
          '$\\dfrac{1}{x^{3}(1+x^{2})}=\\dfrac{1}{x^{3}}-\\dfrac1x+\\dfrac{x}{1+x^{2}}$']
});
add('hard', '중근 부분분수', '(x^2-8*x+7)/(x^2-3*x-10)^2',
    '8/(49*(x-5))-27/(49*(x+2))+30*ln((x-5)/(x+2))/343', {
  domain: [5.5, 9.0], lnAbs: true,
  hints: ['$x^{2}-3x-10=(x-5)(x+2)$ 이므로 분모는 $(x-5)^{2}(x+2)^{2}$ 다.',
          '네 항 $\\dfrac{A}{x-5}+\\dfrac{B}{(x-5)^{2}}+\\dfrac{C}{x+2}+\\dfrac{D}{(x+2)^{2}}$ 로 놓는다.'],
  steps: ['$x=5$ 와 $x=-2$ 를 넣어 $B,D$ 를 먼저 구한다',
          '나머지 계수는 $\\dfrac{30}{343}$ 과 $-\\dfrac{30}{343}$ 이 되어 로그 항이 남는다']
});
add('hard', '지수 치환', 'x*e^x/sqrt(1+e^x)',
    '(2*x-4)*sqrt(1+e^x)-2*ln((sqrt(1+e^x)-1)/(sqrt(1+e^x)+1))', {
  domain: [0.3, 2.0], lnAbs: true,
  hints: ['$v=2\\sqrt{1+e^{x}}$ 로 부분적분한다.',
          '남는 $\\int\\dfrac{2\\sqrt{1+e^{x}}}{1}dx$ 는 $u=\\sqrt{1+e^{x}}$ 로 유리화된다.'],
  steps: ['$=2x\\sqrt{1+e^{x}}-2\\int\\sqrt{1+e^{x}}\\,dx$',
          '$\\int\\sqrt{1+e^{x}}dx=2\\sqrt{1+e^{x}}+\\ln\\left|\\dfrac{\\sqrt{1+e^{x}}-1}{\\sqrt{1+e^{x}}+1}\\right|$']
});
add('hard', '역삼각 부분적분', 'arccos(sqrt(x/(x+1)))',
    'x*arccos(sqrt(x/(x+1)))+sqrt(x)-arctan(sqrt(x))', {
  domain: D.pos,
  hints: ['$dv=dx$ 로 부분적분한다.',
          '$\\left(\\arccos\\sqrt{\\dfrac{x}{x+1}}\\right)\'=-\\dfrac{1}{2\\sqrt x(1+x)}$'],
  steps: ['$=x\\arccos\\sqrt{\\dfrac{x}{x+1}}+\\dfrac12\\int\\dfrac{\\sqrt x}{1+x}dx$',
          '$\\int\\dfrac{\\sqrt x}{1+x}dx=2\\sqrt x-2\\arctan\\sqrt x$']
});
add('hard', '부분적분', 'x*ln(x)/(x^2-1)^(3/2)', 'arctan(sqrt(x^2-1))-ln(x)/sqrt(x^2-1)', {
  domain: D.gt1,
  hints: ['$dv=\\dfrac{x\\,dx}{(x^{2}-1)^{3/2}}\\Rightarrow v=-\\dfrac{1}{\\sqrt{x^{2}-1}}$',
          '남는 적분은 $\\int\\dfrac{dx}{x\\sqrt{x^{2}-1}}=\\arctan\\sqrt{x^{2}-1}$ 다.'],
  steps: ['$=-\\dfrac{\\ln x}{\\sqrt{x^{2}-1}}+\\int\\dfrac{dx}{x\\sqrt{x^{2}-1}}$',
          '$=\\arctan\\sqrt{x^{2}-1}-\\dfrac{\\ln x}{\\sqrt{x^{2}-1}}$']
});
add('hard', '유리식 점화', '1/(x^4-1)^2',
    '3*ln((1+x)/(1-x))/16+3*arctan(x)/8-x/(4*(x^4-1))', {
  domain: D.unit, lnAbs: true,
  hints: ['$\\dfrac{1}{(x^{4}-1)^{2}}$ 는 $\\dfrac{d}{dx}\\dfrac{x}{x^{4}-1}$ 를 이용해 차수를 내린다.',
          '$\\left(\\dfrac{x}{x^{4}-1}\\right)\'=\\dfrac{-3x^{4}-1}{(x^{4}-1)^{2}}$ 에서 시작한다.'],
  steps: ['위 항등식으로 $\\int\\dfrac{dx}{(x^{4}-1)^{2}}$ 를 $\\int\\dfrac{dx}{x^{4}-1}$ 로 환원한다',
          '$\\int\\dfrac{dx}{x^{4}-1}=\\dfrac14\\ln\\left|\\dfrac{x-1}{x+1}\\right|-\\dfrac{\\arctan x}{2}$']
});
add('hard', '유리화 치환', 'sqrt((1-x)/(1+x))/x',
    'ln((sqrt(1+x)-sqrt(1-x))/(sqrt(1+x)+sqrt(1-x)))+2*arctan(sqrt((1-x)/(1+x)))', {
  domain: [0.2, 0.85], lnAbs: true,
  hints: ['$u=\\sqrt{\\dfrac{1-x}{1+x}}$ 로 두면 $x=\\dfrac{1-u^{2}}{1+u^{2}}$ 다.',
          '$dx=-\\dfrac{4u\\,du}{(1+u^{2})^{2}}$ 를 대입하면 유리함수가 된다.'],
  steps: ['$u=\\sqrt{\\dfrac{1-x}{1+x}}$ 로 유리화',
          '$-4\\int\\dfrac{u^{2}du}{(1-u^{2})(1+u^{2})}$ 를 부분분수로 쪼갠다',
          '로그 항과 $\\arctan$ 항이 남는다']
});
add('hard', '부분적분', 'arctan(x)/(1+x)^3',
    'ln((x+1)/sqrt(x^2+1))/4-arctan(x)/(2*(x+1)^2)-1/(4*(x+1))', {
  domain: D.pos, lnAbs: true,
  hints: ['$v=-\\dfrac{1}{2(x+1)^{2}}$ 로 부분적분한다.',
          '남는 $\\int\\dfrac{dx}{2(x+1)^{2}(1+x^{2})}$ 를 부분분수로 쪼갠다.'],
  steps: ['$=-\\dfrac{\\arctan x}{2(x+1)^{2}}+\\dfrac12\\int\\dfrac{dx}{(x+1)^{2}(1+x^{2})}$',
          '부분분수 결과에서 로그 항과 $\\dfrac{1}{x+1}$ 항이 나온다']
});
add('hard', '유리식 점화', '1/(x^2+2*x+10)^3',
    '(arctan((x+1)/3)+3*(x+1)/(x^2+2*x+10)+18*(x+1)/(x^2+2*x+10)^2)/648', {
  domain: [-1.4, 2.0],
  hints: ['$x^{2}+2x+10=(x+1)^{2}+9$ 로 완전제곱한 뒤 $u=x+1$ 로 둔다.',
          '$I_{n}=\\int\\dfrac{du}{(u^{2}+9)^{n}}$ 점화식을 두 번 쓴다.'],
  steps: ['$I_{1}=\\dfrac13\\arctan\\dfrac u3$',
          '$I_{n}=\\dfrac{u}{18(n-1)(u^{2}+9)^{n-1}}+\\dfrac{2n-3}{18(n-1)}I_{n-1}$',
          '$n=2,3$ 을 차례로 적용한다']
});
add('hard', '역삼각 부분적분', 'atan(1/(x^2+x+1))',
    'x*atan(1/(x^2+x+1))+ln((x^2+1)/(x^2+2*x+2))/2+arctan(x+1)', {
  domain: [0.2, 2.4],
  hints: ['$\\arctan\\dfrac{1}{x^{2}+x+1}=\\arctan(x+1)-\\arctan x$ 임을 먼저 확인한다.',
          '덧셈정리 $\\arctan a-\\arctan b=\\arctan\\dfrac{a-b}{1+ab}$ 를 거꾸로 읽는다.'],
  steps: ['$dv=dx$ 로 부분적분',
          '남는 적분은 $\\int\\dfrac{x\\,dx}{1+x^{2}}-\\int\\dfrac{x\\,dx}{1+(x+1)^{2}}$ 로 갈라진다']
});
add('hard', '치환+부분분수', 'x^3/(1+x^6)',
    'ln(x^4-x^2+1)/12-ln(x^2+1)/6+arctan((2*x^2-1)/sqrt(3))/(2*sqrt(3))', {
  domain: [0.3, 2.4],
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\int\\dfrac{u\\,du}{1+u^{3}}$ 다.',
          '$\\dfrac{u}{1+u^{3}}=-\\dfrac{1}{3(u+1)}+\\dfrac{u+1}{3(u^{2}-u+1)}$'],
  steps: ['$u=x^{2}$', '부분분수로 쪼갠 뒤 완전제곱한다',
          '로그 두 항과 $\\arctan$ 한 항이 남는다']
});
add('hard', '치환+부분분수', '(3+x^2)^2*x^3/(1+x^2)^3', 'x^2/2+3*ln(1+x^2)/2+1/(1+x^2)^2', {
  domain: [0.3, 2.4],
  hints: ['$u=1+x^{2}$ 로 두면 $x^{3}dx=\\dfrac{(u-1)du}{2}$ 이고 $3+x^{2}=u+2$ 다.',
          '$\\dfrac{(u+2)^{2}(u-1)}{2u^{3}}$ 를 다항식 나눗셈으로 편다.'],
  steps: ['$(u+2)^{2}(u-1)=u^{3}+3u^{2}-4$',
          '$\\dfrac12\\int\\left(1+\\dfrac3u-\\dfrac{4}{u^{3}}\\right)du=\\dfrac u2+\\dfrac{3\\ln u}{2}+\\dfrac{1}{u^{2}}$']
});
add('hard', '삼각 치환', 'sqrt(1-x^3)/(x^2*sqrt(x))',
    '-2*sqrt((1-x^3)/x^3)/3-2*arcsin(sqrt(x^3))/3', {
  domain: [0.3, 0.9],
  hints: ['$u=x^{3}$ 로 두면 $\\dfrac13\\int\\dfrac{\\sqrt{1-u}}{u^{3/2}}du$ 가 된다.',
          '다시 $u=\\sin^{2}\\theta$ 로 두면 $\\cot^{2}$ 적분이 나온다.'],
  steps: ['$u=x^{3}$', '$\\dfrac13\\int\\dfrac{\\sqrt{1-u}}{u^{3/2}}du$ 를 삼각치환한다',
          '$-\\dfrac23\\sqrt{\\dfrac{1-x^{3}}{x^{3}}}-\\dfrac23\\arcsin\\sqrt{x^{3}}$']
});
add('hard', '쌍곡선 곱', 'cosh(3*x)^2*tanh(2*x)',
    'ln(cosh(2*x))/4+cosh(6*x)/12-cosh(2*x)/2', {
  domain: [0.2, 1.2],
  hints: ['$\\cosh^{2}3x=\\dfrac{\\cosh 6x+1}{2}$ 로 먼저 내린다.',
          '$\\cosh 6x\\tanh 2x$ 는 $\\cosh 6x=\\cosh 2x(4\\cosh^{2}2x-3)$ 로 정리하면 풀린다.'],
  steps: ['$\\cosh^{2}3x\\tanh 2x=\\dfrac{(\\cosh 6x+1)\\tanh 2x}{2}$',
          '$\\int\\tanh 2x\\,dx=\\dfrac{\\ln\\cosh 2x}{2}$ 와 $u=\\cosh 2x$ 치환을 함께 쓴다']
});
add('hard', '삼각 유리식', 'sin(x)^2/(cos(x)^2+cot(x)^2)',
    'tan(x)/2-x+sqrt(2)*arctan(sqrt(2)*tan(x))/4', {
  domain: D.trig,
  hints: ['분자·분모에 $\\sin^{2}x$ 를 곱해 정리하면 $\\dfrac{\\sin^{4}x}{\\sin^{2}x\\cos^{2}x+\\cos^{2}x}$ 다.',
          '$\\cos^{2}x$ 로 나눈 뒤 $u=\\tan x$ 로 둔다.'],
  steps: ['$u=\\tan x$ 로 두면 유리함수가 된다',
          '$\\int\\dfrac{u^{4}\\,du}{(1+u^{2})(u^{2}+ \\cdots)}$ 를 가분수 나눗셈 + 부분분수로 푼다']
});
add('hard', '곱-합 + 순환', 'e^(13*x)*sin(2*x)*cos(5*x)',
    'e^(13*x)*(13*sin(7*x)-7*cos(7*x))/436-e^(13*x)*(13*sin(3*x)-3*cos(3*x))/356', {
  domain: [0.05, 0.5],
  hints: ['$\\sin 2x\\cos 5x=\\dfrac{\\sin 7x-\\sin 3x}{2}$ 로 먼저 합으로 바꾼다.',
          '$\\int e^{ax}\\sin bx\\,dx=\\dfrac{e^{ax}(a\\sin bx-b\\cos bx)}{a^{2}+b^{2}}$'],
  steps: ['곱을 합으로 바꾼다', '$a=13,\;b=7$ 과 $b=3$ 을 각각 공식에 넣는다',
          '분모는 $169+49=218$ 과 $169+9=178$ 이다']
});
add('hard', '부분적분', 'x*tanh(x)^2', 'x^2/2-x*tanh(x)+ln(cosh(x))', {
  domain: D.hypP,
  hints: ['$\\tanh^{2}=1-\\operatorname{sech}^{2}$ 로 쪼갠다.',
          '$\\int x\\operatorname{sech}^{2}x\\,dx=x\\tanh x-\\ln\\cosh x$'],
  steps: ['$\\int x\\,dx-\\int x\\operatorname{sech}^{2}x\\,dx$',
          '$=\\dfrac{x^{2}}{2}-x\\tanh x+\\ln\\cosh x$']
});

// --- 몬스터
add('monster', '숨은 구조', '1/(cos(x)*sqrt(cos(2*x)))', 'arctan(sin(x)/sqrt(cos(2*x)))', {
  domain: [0.1, 0.7],
  hints: ['$\\cos 2x=1-2\\sin^{2}x$ 로 바꾸고 $u=\\sin x$ 로 둔다.',
          '$\\int\\dfrac{du}{(1-u^{2})\\sqrt{1-2u^{2}}}$ 가 된다.'],
  steps: ['$u=\\sin x,\;du=\\cos x\\,dx$ (분자·분모에 $\\cos x$ 를 곱한다)',
          '$g=\\dfrac{u}{\\sqrt{1-2u^{2}}}$ 로 두면 $\\arctan g$ 의 도함수와 일치한다',
          '$=\\arctan\\dfrac{\\sin x}{\\sqrt{\\cos 2x}}$']
});
add('monster', '역수 치환', '(x^4-1)/(x^2*sqrt(x^4-x^2+1))', 'sqrt(x^4-x^2+1)/x', {
  domain: [0.3, 2.6],
  hints: ['답을 $\\dfrac{\\sqrt{x^{4}-x^{2}+1}}{x}$ 로 놓고 몫의 미분법을 확인해 본다.',
          '분자에서 $x^{4}-1$ 이 정확히 떨어진다.'],
  steps: ['$F=\\dfrac{\\sqrt{x^{4}-x^{2}+1}}{x}$',
          '$F\'=\\dfrac{x\\cdot\\frac{4x^{3}-2x}{2\\sqrt{\\cdot}}-\\sqrt{\\cdot}}{x^{2}}=\\dfrac{x^{4}-1}{x^{2}\\sqrt{x^{4}-x^{2}+1}}$']
});
add('monster', '역수 치환', '(x^2-1)/(x*sqrt(x^4+3*x^2+1))',
    'ln((x^2+1+sqrt(x^4+3*x^2+1))/x)', {
  domain: [0.3, 2.6], lnAbs: true,
  hints: ['분자·분모를 $x^{2}$ 로 나누고 $u=x+\\dfrac1x$ 로 둔다.',
          '$x^{2}+3+\\dfrac{1}{x^{2}}=u^{2}+1$ 이므로 $\\int\\dfrac{du}{\\sqrt{u^{2}+1}}$ 가 된다.'],
  steps: ['$u=x+\\dfrac1x,\;du=\\left(1-\\dfrac{1}{x^{2}}\\right)dx$',
          '$\\int\\dfrac{du}{\\sqrt{u^{2}+1}}=\\ln\\left|u+\\sqrt{u^{2}+1}\\right|$',
          '되돌리면 $\\ln\\dfrac{x^{2}+1+\\sqrt{x^{4}+3x^{2}+1}}{x}$']
});
add('monster', '역수 치환', 'sqrt(x^4+x^2+1)/x',
    '(asinh((2*x^2+1)/sqrt(3))+2*sqrt(x^4+x^2+1)-2*atanh((x^2+2)/(2*sqrt(x^4+x^2+1))))/4', {
  domain: [0.35, 2.4],
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\int\\dfrac{\\sqrt{u^{2}+u+1}}{u}du$ 다.',
          '$u^{2}+u+1=\\left(u+\\dfrac12\\right)^{2}+\\dfrac34$ 로 완전제곱한 뒤 쌍곡선 치환.'],
  steps: ['$u=x^{2}$ 로 차수를 낮춘다',
          '완전제곱 후 $\\int\\dfrac{\\sqrt{t^{2}+a^{2}}}{t-\\frac12}dt$ 꼴로 정리한다',
          '$\\operatorname{arsinh}$, 근호, $\\operatorname{artanh}$ 세 항이 나온다']
});
add('monster', '지수 치환', 'e^x*(2*e^x+1)/((e^(2*x)+e^x+1)*sqrt(e^(2*x)+e^x))',
    '2*arctan(sqrt(e^(2*x)+e^x))', {
  domain: [0.2, 2.0],
  hints: ['$u=\\sqrt{e^{2x}+e^{x}}$ 로 두면 $2u\\,du=e^{x}(2e^{x}+1)dx$ 다.',
          '분모의 $e^{2x}+e^{x}+1$ 은 정확히 $u^{2}+1$ 이다.'],
  steps: ['$u=\\sqrt{e^{2x}+e^{x}}$', '$\\int\\dfrac{2\\,du}{u^{2}+1}=2\\arctan u$']
});
add('monster', '미분 꼴 알아보기', 'e^x*(2-2*x^2-x)/(2*x^2*sqrt(x+1))', '-e^x*sqrt(x+1)/x', {
  domain: [0.3, 2.4],
  hints: ['답을 $-\\dfrac{e^{x}\\sqrt{x+1}}{x}$ 로 놓고 미분해 본다.',
          '$\\int e^{x}(f+f\')dx=e^{x}f$ 에서 $f=-\\dfrac{\\sqrt{x+1}}{x}$ 다.'],
  steps: ['$f=-\\dfrac{\\sqrt{x+1}}{x}$',
          '$f\'=\\dfrac{\\sqrt{x+1}}{x^{2}}-\\dfrac{1}{2x\\sqrt{x+1}}$',
          '$f+f\'$ 를 통분하면 피적분함수가 나온다']
});
add('monster', '미분 꼴 알아보기', 'e^x*(2-x^2)/((1-x)*sqrt(1-x^2))', 'e^x*sqrt(1+x)/sqrt(1-x)', {
  domain: [-0.7, 0.7],
  hints: ['$\\int e^{x}(f+f\')dx=e^{x}f$ 를 노린다.',
          '$f=\\sqrt{\\dfrac{1+x}{1-x}}$ 로 두고 $f\'$ 를 계산해 본다.'],
  steps: ['$f=\\sqrt{\\dfrac{1+x}{1-x}},\;f\'=\\dfrac{1}{(1-x)\\sqrt{1-x^{2}}}$',
          '$f+f\'=\\dfrac{2-x^{2}}{(1-x)\\sqrt{1-x^{2}}}$']
});
add('monster', '미분 꼴 알아보기', '(1-x-x^2)/(e^x*(x-2)^2)', '(x+3)/(e^x*(x-2))', {
  domain: [0.2, 1.7],
  hints: ['$\\dfrac{P(x)}{e^{x}(x-2)}$ 꼴로 답을 놓고 미정계수로 $P$ 를 찾는다.',
          '$P=x+3$ 을 넣어 미분하면 분자가 $1-x-x^{2}$ 이 된다.'],
  steps: ['$F=\\dfrac{(ax+b)e^{-x}}{x-2}$ 로 놓고 미분한다',
          '$-ax^{2}+(2a-b)x+(b-2a)=1-x-x^{2}$ 에서 $a=1,\;b=3$']
});
add('monster', '미분 꼴 알아보기',
    'e^x*(2*x^6-3*x^5+2*x^4-x^3+2*x+2)/(2*(x^5+x^3+1)^(3/2))', 'x*e^x/sqrt(x^5+x^3+1)', {
  domain: [0.2, 1.6],
  hints: ['답을 $\\dfrac{xe^{x}}{\\sqrt{x^{5}+x^{3}+1}}$ 로 놓고 곱·몫의 미분법을 적용한다.',
          '$\\int e^{x}(f+f\')dx=e^{x}f$ 에서 $f=\\dfrac{x}{\\sqrt{x^{5}+x^{3}+1}}$ 다.'],
  steps: ['$f=\\dfrac{x}{\\sqrt{x^{5}+x^{3}+1}}$',
          '$f+f\'$ 를 통분하면 분모가 $2(x^{5}+x^{3}+1)^{3/2}$ 이 된다']
});
add('monster', '중첩 역삼각',
    'sin(x)^3/((cos(x)^4+3*cos(x)^2+1)*arctan(sec(x)+cos(x)))',
    'ln(arctan(sec(x)+cos(x)))', {
  domain: D.trig, lnAbs: true,
  hints: ['$w=\\sec x+\\cos x$ 로 두면 $w\'=\\dfrac{\\sin^{3}x}{\\cos^{2}x}$ 다.',
          '$1+w^{2}=\\dfrac{\\cos^{4}x+3\\cos^{2}x+1}{\\cos^{2}x}$ 임을 확인하면 전부 약분된다.'],
  steps: ['$w=\\sec x+\\cos x,\;\\theta=\\arctan w$',
          '$\\theta\'=\\dfrac{w\'}{1+w^{2}}=\\dfrac{\\sin^{3}x}{\\cos^{4}x+3\\cos^{2}x+1}$',
          '$\\int\\dfrac{\\theta\'}{\\theta}dx=\\ln|\\theta|$']
});
add('monster', '몫의 미분 되짚기', 'x^2*(x*sec(x)^2+tan(x))/(x*tan(x)+1)^2',
    '2*ln(x*sin(x)+cos(x))-x^2/(x*tan(x)+1)', {
  domain: D.trig, lnAbs: true,
  hints: ['$(x\\tan x+1)\'=x\\sec^{2}x+\\tan x$ 라는 점이 열쇠다.',
          '$\\dfrac{x^{2}}{x\\tan x+1}$ 를 미분해 보고 남는 항을 정리한다.'],
  steps: ['$D=x\\tan x+1,\;D\'=x\\sec^{2}x+\\tan x$',
          '$\\left(\\dfrac{x^{2}}{D}\\right)\'=\\dfrac{2x}{D}-\\dfrac{x^{2}D\'}{D^{2}}$',
          '$\\dfrac{2x}{D}=\\dfrac{2x\\cos x}{x\\sin x+\\cos x}$ 는 로그로 적분된다']
});
add('monster', '지수탑 미분',
    'e^(x*sin(x)+cos(x))*(x^4*cos(x)^3-x*sin(x)+cos(x))/(x^2*cos(x)^2)',
    'e^(x*sin(x)+cos(x))*(x-1/(x*cos(x)))', {
  domain: [0.3, 1.1],
  hints: ['$(x\\sin x+\\cos x)\'=x\\cos x$ 임을 먼저 확인한다.',
          '$\\int e^{g}(f g\'+f\')dx=e^{g}f$ 꼴로 보고 $f=x-\\dfrac{1}{x\\cos x}$ 를 시험한다.'],
  steps: ['$g=x\\sin x+\\cos x,\;g\'=x\\cos x$',
          '$f=x-\\dfrac{1}{x\\cos x}$ 로 두고 $fg\'+f\'$ 를 계산한다',
          '통분하면 정확히 피적분함수가 된다']
});
add('monster', '쌍곡선 유리식', 'e^(2*x)/sinh(x)^4',
    '-8*(1-3*e^(2*x)+3*e^(4*x))/(3*(e^(2*x)-1)^3)', {
  domain: [0.3, 1.6],
  hints: ['$\\sinh x=\\dfrac{e^{x}-e^{-x}}{2}$ 를 대입해 전부 $e^{x}$ 로 바꾼다.',
          '$u=e^{2x}$ 로 두면 $8\\int\\dfrac{u\\,du}{2(u-1)^{4}}$ 꼴이 된다.'],
  steps: ['$\\sinh^{4}x=\\dfrac{(e^{2x}-1)^{4}}{16e^{2x}}$',
          '$u=e^{2x}$ 로 두고 $u=(u-1)+1$ 로 쪼갠다',
          '$(u-1)^{-3}$ 과 $(u-1)^{-4}$ 항이 나온다']
});
add('monster', '역삼각 지수', 'x^2*e^(arcsin(x))',
    'e^(arcsin(x))*(3*x^3/10-x/10+sqrt(1-x^2)/5-(1-x^2)^(3/2)/10)', {
  domain: D.unit,
  hints: ['$t=\\arcsin x$ 로 두면 $\\int e^{t}\\sin^{2}t\\cos t\\,dt$ 가 된다.',
          '$\\sin^{2}t\\cos t$ 를 배각으로 펴면 $e^{t}\\cos$ 형 순환 적분 두 개가 된다.'],
  steps: ['$t=\\arcsin x,\;dx=\\cos t\\,dt$',
          '$\\sin^{2}t\\cos t=\\dfrac{\\cos t-\\cos 3t}{4}$',
          '$\\int e^{t}\\cos kt\\,dt$ 공식을 $k=1,3$ 에 적용한다']
});
add('monster', '고차 역수 치환', '1/(x^11*sqrt(1+x^4))',
    '-((1+x^4)/x^4)^(5/2)/10+((1+x^4)/x^4)^(3/2)/3-sqrt((1+x^4)/x^4)/2', {
  domain: [0.6, 1.8],
  hints: ['$u=\\dfrac{\\sqrt{1+x^{4}}}{x^{2}}$ 로 두면 $u^{2}=1+\\dfrac{1}{x^{4}}$ 다.',
          '$du=-\\dfrac{2\\,dx}{x^{5}\\sqrt{1+x^{4}}}\\cdot x^{2}$ 를 정리하면 $u$ 의 다항식만 남는다.'],
  steps: ['$u^{2}=\\dfrac{1+x^{4}}{x^{4}}$ 로 두면 $\\dfrac{1}{x^{4}}=u^{2}-1$',
          '$-\\dfrac12\\int(u^{2}-1)^{2}du$ 꼴로 바뀐다',
          '전개해 항별로 적분한다']
});
add('monster', '가분수 + 완전제곱', '(x^7+2)/(x^2+x+1)^2',
    'x/(x^2+x+1)+2*arctan((2*x+1)/sqrt(3))/sqrt(3)-2*ln(x^2+x+1)+x^4/4-2*x^3/3+x^2/2+2*x', {
  domain: [0.3, 2.4],
  hints: ['먼저 $x^{7}+2$ 를 $(x^{2}+x+1)^{2}$ 로 나눠 다항식 몫과 나머지를 구한다.',
          '나머지 부분은 $\\dfrac{1}{(x^{2}+x+1)^{2}}$ 점화식으로 처리한다.'],
  steps: ['다항식 나눗셈으로 4차 몫을 뽑는다',
          '$x^{2}+x+1=\\left(x+\\dfrac12\\right)^{2}+\\dfrac34$ 로 완전제곱',
          '점화식으로 차수를 내리면 $\\arctan$ 항과 로그 항이 남는다']
});
add('monster', '로그 부분적분', 'csc(x)^2*ln(cos(x)+sqrt(cos(2*x)))',
    '-cot(x)*ln(cos(x)+sqrt(cos(2*x)))+sqrt(cos(2*x))/sin(x)-cot(x)-x', {
  domain: [0.1, 0.65],
  hints: ['$dv=\\csc^{2}x\\,dx\\Rightarrow v=-\\cot x$ 로 부분적분한다.',
          '$\\left(\\ln(\\cos x+\\sqrt{\\cos 2x})\\right)\'=-\\dfrac{\\sin x}{\\sqrt{\\cos 2x}}$ 임을 확인한다.'],
  steps: ['$=-\\cot x\\ln(\\cos x+\\sqrt{\\cos 2x})-\\int\\dfrac{\\cos x}{\\sqrt{\\cos 2x}}dx$',
          '남는 적분은 $\\cos 2x=1-2\\sin^{2}x$ 로 두고 정리한다']
});

// ================================================================== 정적분 (올림피아드)
// 문제식 출처: 300 Integral Practice Set (Maths Olympiad Preparation, 2024) 정적분 파트.
// 값은 전부 이중지수 구적으로 다시 확인했다.

// ------------------------------------------------------------------ 어려움
addDef('hard', '반각 치환', '1/(sin(2*x)+cos(2*x)+1)', 'ln(2)/2', { lo: '0', hi: 'pi/4',
  hints: ['배각공식으로 $\\sin 2x=2\\sin x\\cos x$, $1+\\cos 2x=2\\cos^{2}x$ 를 넣는다.',
          '분모가 $2\\cos x(\\sin x+\\cos x)$ 로 묶여 $\\dfrac{\\sec^{2}x}{2(\\tan x+1)}$ 가 된다.'],
  steps: ['$u=\\tan x$ 로 두면 $\\dfrac12\\int_{0}^{1}\\dfrac{du}{u+1}$',
          '$=\\dfrac{\\ln 2}{2}$'] });

addDef('hard', '부분적분', 'x*arcsin(x)/sqrt(1-x^2)', '(6-sqrt(3)*pi)/12', { lo: '0', hi: '1/2',
  hints: ['$dv=\\dfrac{x\\,dx}{\\sqrt{1-x^{2}}}\\Rightarrow v=-\\sqrt{1-x^{2}}$ 로 부분적분한다.',
          '남는 적분은 $\\int dx$ 로 줄어든다.'],
  steps: ['$\\left[-\\sqrt{1-x^{2}}\\arcsin x\\right]_{0}^{1/2}+\\int_{0}^{1/2}dx$',
          '$=-\\dfrac{\\sqrt3}{2}\\cdot\\dfrac{\\pi}{6}+\\dfrac12=\\dfrac{6-\\sqrt3\\pi}{12}$'] });

addDef('hard', '부분적분', 'ln(x)/sqrt(x)', '4-2*sqrt(e)', { lo: '1', hi: 'e',
  hints: ['$v=2\\sqrt x$ 로 부분적분한다.', '$\\int\\dfrac{\\ln x}{\\sqrt x}dx=2\\sqrt x(\\ln x-2)$'],
  steps: ['$\\left[2\\sqrt x(\\ln x-2)\\right]_{1}^{e}$', '$=2\\sqrt e(1-2)-2(0-2)=4-2\\sqrt e$'] });

addDef('hard', '삼각 유리화', '(1-sin(x))/(1+sin(x))', '4-pi', { lo: '0', hi: 'pi',
  hints: ['분자·분모에 $1-\\sin x$ 를 곱해 분모를 $\\cos^{2}x$ 로 만든다.',
          '$\\sec^{2}x-2\\sec x\\tan x+\\tan^{2}x$ 로 펴진다.'],
  steps: ['$\\dfrac{(1-\\sin x)^{2}}{\\cos^{2}x}=\\sec^{2}x-2\\sec x\\tan x+\\sec^{2}x-1$',
          '원시함수는 $2\\tan x-2\\sec x-x$', '끝점 극한을 조심해서 대입하면 $4-\\pi$'] });

addDef('hard', '치환적분', 'sin(2*x)/(2+cos(x))', '1+4*ln(5/6)', { lo: '0', hi: 'pi/3',
  hints: ['$\\sin 2x=2\\sin x\\cos x$ 로 펴고 $u=2+\\cos x$ 로 둔다.',
          '$\\cos x=u-2$ 이므로 $-2\\int\\dfrac{u-2}{u}du$ 가 된다.'],
  steps: ['$u=2+\\cos x,\;du=-\\sin x\\,dx$',
          '$-2\\int_{3}^{5/2}\\left(1-\\dfrac2u\\right)du=1+4\\ln\\dfrac56$'] });

addDef('hard', '치환적분', 'cos(x)/(2-sin(2*x))', 'pi/4', { lo: '0', hi: 'pi/2',
  hints: ['$2-\\sin 2x=1+(\\sin x-\\cos x)^{2}$ 로 완전제곱된다.',
          '$u=\\sin x-\\cos x$ 로 두면 $du=(\\cos x+\\sin x)dx$ — 대칭을 쓴다.'],
  steps: ['$x\\to\\frac\\pi2-x$ 로 두면 $\\int\\cos\\to\\int\\sin$ 이므로 둘을 더해 $2I$ 를 만든다',
          '$2I=\\int_{0}^{\\pi/2}\\dfrac{\\cos x+\\sin x}{1+(\\sin x-\\cos x)^{2}}dx=\\left[\\arctan u\\right]_{-1}^{1}=\\dfrac\\pi2$'] });

addDef('hard', '완전제곱', '1/((x+1)*sqrt(x^2+2*x+2))', 'ln(sqrt(3/2))',
  { lo: 'sqrt(3)-1', hi: '2*sqrt(2)-1',
  hints: ['$x^{2}+2x+2=(x+1)^{2}+1$ 로 완전제곱하고 $t=x+1$ 로 둔다.',
          '$\\int\\dfrac{dt}{t\\sqrt{t^{2}+1}}=\\ln\\dfrac{t}{1+\\sqrt{t^{2}+1}}$'],
  steps: ['$t=x+1$ 이면 적분 구간은 $\\sqrt3$ 에서 $2\\sqrt2$ 까지',
          '$\\left[\\ln\\dfrac{t}{1+\\sqrt{t^{2}+1}}\\right]_{\\sqrt3}^{2\\sqrt2}=\\ln\\sqrt{\\dfrac32}$'] });

addDef('hard', '부분분수', '(x^4+81)/(x*(x^2+9)^2)', '1/10+9/(e^2+9)', { lo: '1', hi: 'e',
  hints: ['$x^{4}+81=(x^{2}+9)^{2}-18x^{2}$ 로 쓰면 두 조각으로 갈라진다.',
          '$\\dfrac{1}{x}-\\dfrac{18x}{(x^{2}+9)^{2}}$ 만 남는다.'],
  steps: ['$\\dfrac{x^{4}+81}{x(x^{2}+9)^{2}}=\\dfrac1x-\\dfrac{18x}{(x^{2}+9)^{2}}$',
          '원시함수는 $\\ln x+\\dfrac{9}{x^{2}+9}$', '끝점을 대입한다'] });

addDef('hard', '부분분수', '(x^2+2*x-1)/(2*x^3+3*x^2-2*x)', 'ln(72)/10', { lo: '1', hi: '2',
  hints: ['$2x^{3}+3x^{2}-2x=x(2x-1)(x+2)$ 로 인수분해한다.',
          '가리기(cover-up)로 세 계수를 한 번에 구한다.'],
  steps: ['$\\dfrac{1/2}{x}+\\dfrac{1/10}{2x-1}\\cdot 2-\\dfrac{1/10}{x+2}$ 꼴로 갈라진다',
          '로그를 모아 끝점을 대입하면 $\\dfrac{\\ln 72}{10}$'] });

addDef('hard', '순환 부분적분', 'e^(-x)*sin(2*x)^2', '(8-8*e^(-pi))/17', { lo: '0', hi: 'pi',
  hints: ['$\\sin^{2}2x=\\dfrac{1-\\cos 4x}{2}$ 로 먼저 내린다.',
          '$\\int e^{-x}\\cos 4x\\,dx=\\dfrac{e^{-x}(-\\cos 4x+4\\sin 4x)}{17}$'],
  steps: ['$\\dfrac12\\int_{0}^{\\pi}e^{-x}dx-\\dfrac12\\int_{0}^{\\pi}e^{-x}\\cos 4x\\,dx$',
          '두 값을 합치면 $\\dfrac{8(1-e^{-\\pi})}{17}$'] });

addDef('hard', '삼각함수 고차', 'tan(x)^4/(1-tan(x)^2)', 'pi/12-sqrt(3)/3+atanh(1/sqrt(3))/2',
  { lo: '0', hi: 'pi/6',
  hints: ['$\\dfrac{t^{4}}{1-t^{2}}=-t^{2}-1+\\dfrac{1}{1-t^{2}}$ 로 다항식 나눗셈을 한다.',
          '$t=\\tan x$ 이므로 $\\int\\tan^{2}$ 와 $\\int\\dfrac{dx}{1-\\tan^{2}x}$ 로 갈린다.'],
  steps: ['나눗셈으로 세 조각으로 나눈다',
          '$\\int\\dfrac{dx}{1-\\tan^{2}x}=\\dfrac12\\operatorname{artanh}(\\tan x)$ 를 쓴다'] });

addDef('hard', '유리식 극한', '1/(1+x^4)', 'pi/(2*sqrt(2))', { lo: '0', hi: 'inf',
  hints: ['$x\\to\\frac1x$ 대칭을 쓰거나, $u=x-\\dfrac1x$ 치환으로 간다.',
          '$\\dfrac{1}{1+x^{4}}=\\dfrac12\\cdot\\dfrac{x^{2}+1}{x^{4}+1}-\\dfrac12\\cdot\\dfrac{x^{2}-1}{x^{4}+1}$'],
  steps: ['$\\int_{0}^{\\infty}\\dfrac{x^{2}+1}{x^{4}+1}dx=\\dfrac{\\pi}{\\sqrt2}$ (여기서 $u=x-\\frac1x$)',
          '$\\int_{0}^{\\infty}\\dfrac{x^{2}-1}{x^{4}+1}dx=0$ (로그 항이 상쇄)',
          '따라서 $\\dfrac{\\pi}{2\\sqrt2}$'] });

addDef('hard', '쌍곡선함수', 'sech(x)', 'pi', { lo: '-inf', hi: 'inf',
  hints: ['$\\int\\operatorname{sech}x\\,dx=\\arctan(\\sinh x)$ 다.',
          '$\\sinh x$ 는 $\\pm\\infty$ 로 가므로 $\\arctan$ 이 $\\pm\\frac\\pi2$ 에 닿는다.'],
  steps: ['$\\left[\\arctan(\\sinh x)\\right]_{-\\infty}^{\\infty}$',
          '$=\\dfrac\\pi2-\\left(-\\dfrac\\pi2\\right)=\\pi$'] });

addDef('hard', '유명한 근사', 'x^4*(1-x)^4/(1+x^2)', '22/7-pi', { lo: '0', hi: '1',
  hints: ['분자를 전개해 $1+x^{2}$ 로 나누면 다항식 + $\\dfrac{4}{1+x^{2}}$ 가 된다.',
          '적분값이 양수라는 사실이 곧 $\\dfrac{22}{7}>\\pi$ 의 증명이다.'],
  steps: ['$\\dfrac{x^{4}(1-x)^{4}}{1+x^{2}}=x^{6}-4x^{5}+5x^{4}-4x^{2}+4-\\dfrac{4}{1+x^{2}}$',
          '항별로 적분하면 $\\dfrac{22}{7}-\\pi$'] });

addDef('hard', '파인만 기법', 'ln(x+1)/(x^2-x+1)', 'pi*ln(3)/(2*sqrt(3))', { lo: '0', hi: '2',
  hints: ['$\\dfrac{x+1}{x^{3}+1}=\\dfrac{1}{x^{2}-x+1}$ 임을 이용해 꼴을 바꿔 본다.',
          '$x\\to\\dfrac{2-x}{1+x}$ 로 두면 구간이 자기 자신으로 돌아온다.'],
  steps: ['치환 $x\\mapsto\\dfrac{2-x}{1+x}$ 로 $I$ 를 다시 쓴다',
          '두 표현을 더하면 $\\ln 3$ 이 상수로 빠져나온다',
          '$2I=\\ln 3\\int_{0}^{2}\\dfrac{dx}{x^{2}-x+1}$'] });

addDef('hard', '삼각 항등식', '(sec(x)+csc(x))*(sec(x)+tan(x))/(csc(x)+cot(x))',
  '1+2/sqrt(3)', { lo: '0', hi: 'pi/3',
  hints: ['$\\dfrac{\\sec x+\\tan x}{\\csc x+\\cot x}=\\tan x$ 로 간단해진다.',
          '$(\\sec x+\\csc x)\\tan x=\\sec x\\tan x+\\sec x$ 다.'],
  steps: ['$(\\sec x+\\csc x)\\tan x=\\sec x\\tan x+\\sec x$',
          '원시함수는 $\\sec x+\\ln|\\sec x+\\tan x|$ … 가 아니라 정리하면 $\\sec x+\\tan x$ 형태로 떨어진다',
          '끝점을 대입하면 $1+\\dfrac{2}{\\sqrt3}$'] });

// ------------------------------------------------------------------ 몬스터
addDef('monster', '급수 전개', 'ln(x)/(x-1)', 'pi^2/6', { lo: '0', hi: '1',
  hints: ['$\\dfrac{1}{1-x}=\\sum_{n\\ge 0}x^{n}$ 로 펴고 항별로 적분한다.',
          '$\\int_{0}^{1}x^{n}\\ln x\\,dx=-\\dfrac{1}{(n+1)^{2}}$'],
  steps: ['$-\\int_{0}^{1}\\dfrac{\\ln x}{1-x}dx=-\\sum_{n\\ge0}\\int_{0}^{1}x^{n}\\ln x\\,dx$',
          '$=\\sum_{n\\ge1}\\dfrac{1}{n^{2}}=\\zeta(2)=\\dfrac{\\pi^{2}}{6}$'] });

addDef('monster', '급수 전개', 'ln(x)/(x+1)', '-pi^2/12', { lo: '0', hi: '1',
  hints: ['$\\dfrac{1}{1+x}=\\sum_{n\\ge0}(-1)^{n}x^{n}$ 로 펴서 항별로 적분한다.',
          '교대급수 $\\sum\\dfrac{(-1)^{n}}{n^{2}}=-\\dfrac{\\pi^{2}}{12}$ 를 쓴다.'],
  steps: ['$\\sum_{n\\ge0}(-1)^{n}\\int_{0}^{1}x^{n}\\ln x\\,dx=-\\sum_{n\\ge1}\\dfrac{(-1)^{n-1}}{n^{2}}$',
          '$=-\\dfrac{\\pi^{2}}{12}$'] });

addDef('monster', '대칭 논법', 'ln(cos(x))', '-pi*ln(2)/2', { lo: '0', hi: 'pi/2',
  hints: ['$x\\to\\frac\\pi2-x$ 로 두면 $\\int\\ln\\cos=\\int\\ln\\sin$ 임을 얻는다.',
          '둘을 더하고 $\\sin x\\cos x=\\frac{\\sin 2x}{2}$ 를 쓴다.'],
  steps: ['$2I=\\int_{0}^{\\pi/2}\\ln\\dfrac{\\sin 2x}{2}dx$',
          '$u=2x$ 로 두면 오른쪽이 다시 $I$ 가 되어 $2I=I-\\dfrac\\pi2\\ln2$',
          '$I=-\\dfrac{\\pi\\ln 2}{2}$'] });

addDef('monster', '급수 전개', 'ln(1+x^2)/(1+x)', '3*ln(2)^2/4-pi^2/48', { lo: '0', hi: '1',
  hints: ['$\\ln(1+x^{2})=\\ln(1+x)+\\ln(1-x)+\\ln\\dfrac{1+x^{2}}{1-x^{2}}$ 같은 분해를 시도한다.',
          '또는 $I(a)=\\int_{0}^{1}\\dfrac{\\ln(1+a x^{2})}{1+x}dx$ 로 두고 $a$ 로 미분한다.'],
  steps: ['파인만 기법: $I\'(a)=\\int_{0}^{1}\\dfrac{x^{2}}{(1+ax^{2})(1+x)}dx$',
          '부분분수로 쪼갠 뒤 $a$ 에 대해 $0$ 에서 $1$ 까지 적분한다'] });

addDef('monster', '대칭 논법', 'ln(2+tan(x)^2)', 'pi*ln(sqrt(2)+1)', { lo: '0', hi: 'pi/2',
  hints: ['$2+\\tan^{2}x=\\dfrac{1+\\cos^{2}x}{\\cos^{2}x}$ 로 정리한다.',
          '$\\int_{0}^{\\pi/2}\\ln(a^{2}\\cos^{2}x+b^{2}\\sin^{2}x)dx=\\pi\\ln\\dfrac{a+b}{2}$ 를 쓴다.'],
  steps: ['$\\ln(1+\\cos^{2}x)-2\\ln\\cos x$ 로 나눈다',
          '앞 항에 $a=\\sqrt2,\;b=1$ 공식을, 뒤 항에 $\\int\\ln\\cos=-\\frac\\pi2\\ln2$ 를 쓴다',
          '$=\\pi\\ln(\\sqrt2+1)$'] });

addDef('monster', '제타 함수', 'x/(e^x+1)', 'pi^2/12', { lo: '0', hi: 'inf',
  hints: ['$\\dfrac{1}{e^{x}+1}=\\sum_{n\\ge1}(-1)^{n-1}e^{-nx}$ 로 편다.',
          '$\\int_{0}^{\\infty}xe^{-nx}dx=\\dfrac{1}{n^{2}}$'],
  steps: ['$\\sum_{n\\ge1}\\dfrac{(-1)^{n-1}}{n^{2}}=\\eta(2)=\\dfrac{\\zeta(2)}{2}$',
          '$=\\dfrac{\\pi^{2}}{12}$'] });

addDef('monster', '급수 전개', 'ln(1+e^(-x))', 'pi^2/12', { lo: '0', hi: 'inf',
  hints: ['$\\ln(1+t)=\\sum_{n\\ge1}\\dfrac{(-1)^{n-1}t^{n}}{n}$ 에 $t=e^{-x}$ 를 넣는다.',
          '부분적분하면 앞 문제 $\\int_{0}^{\\infty}\\dfrac{x}{e^{x}+1}dx$ 와 같아진다.'],
  steps: ['$\\sum_{n\\ge1}\\dfrac{(-1)^{n-1}}{n}\\int_{0}^{\\infty}e^{-nx}dx=\\sum_{n\\ge1}\\dfrac{(-1)^{n-1}}{n^{2}}$',
          '$=\\dfrac{\\pi^{2}}{12}$'] });

addDef('monster', '파인만 기법', '(x-1)/((1+x^3)*ln(x))', 'ln(3)/2', { lo: '0', hi: '1',
  hints: ['$\\dfrac{x^{a}-1}{\\ln x}=\\int_{0}^{a}x^{t}dt$ 라는 표현을 쓴다.',
          '적분 순서를 바꾸면 $\\int_{0}^{1}\\dfrac{x^{t}}{1+x^{3}}dx$ 가 남는다.'],
  steps: ['$I=\\int_{0}^{1}\\int_{0}^{1}\\dfrac{x^{t}}{1+x^{3}}dt\\,dx$',
          '순서를 바꿔 $t$ 로 먼저 적분한다', '$=\\dfrac{\\ln 3}{2}$'] });

addDef('monster', '대칭 논법', 'ln(tan(x))/(1-tan(x)+tan(x)^2)', '-7*pi^2/72', { lo: '0', hi: 'pi/2',
  hints: ['$u=\\tan x$ 로 두면 $\\int_{0}^{\\infty}\\dfrac{\\ln u}{(1-u+u^{2})(1+u^{2})}du$ 다.',
          '$u\\to\\dfrac1u$ 대칭으로 구간을 $[0,1]$ 로 접는다.'],
  steps: ['$u=\\tan x$ 치환',
          '$u\\to 1/u$ 로 접으면 $\\ln u$ 의 부호가 뒤집혀 조합이 단순해진다',
          '남은 적분을 급수로 펴면 $-\\dfrac{7\\pi^{2}}{72}$'] });

addDef('monster', '대칭 논법', 'ln(tan(x))/(1+tan(x)^3)', '-37*pi^2/432', { lo: '0', hi: 'pi/2',
  hints: ['앞 문제와 같은 $u=\\tan x$ 치환에서 시작한다.',
          '$1+u^{3}=(1+u)(1-u+u^{2})$ 로 인수분해한 뒤 부분분수를 쓴다.'],
  steps: ['$u=\\tan x$ 로 두고 $u\\to1/u$ 대칭을 쓴다',
          '$\\int_{0}^{1}\\dfrac{\\ln u}{1+u}$, $\\int_{0}^{1}\\dfrac{u\\ln u}{1-u+u^{2}}$ 등으로 갈라진다'] });

addDef('monster', '대칭 논법', '(1-x^99)/((1+x)*(1+x^100))', '99*ln(2)/100', { lo: '0', hi: '1',
  hints: ['$x\\to\\dfrac1x$ 로 두면 $[1,\\infty)$ 조각과 짝이 맞는다.',
          '$\\dfrac{1-x^{99}}{(1+x)(1+x^{100})}$ 를 $\\dfrac{1}{1+x}-\\dfrac{x^{99}+\\cdots}{\\cdots}$ 로 정리해 본다.'],
  steps: ['$I=\\int_{0}^{1}\\dfrac{dx}{1+x}-\\int_{0}^{1}\\dfrac{x^{99}(1+x)}{(1+x)(1+x^{100})}dx$ 꼴로 나눈다',
          '뒤 항은 $u=x^{100}$ 치환으로 $\\dfrac{\\ln 2}{100}$',
          '$=\\ln 2-\\dfrac{\\ln 2}{100}=\\dfrac{99\\ln 2}{100}$'] });

addDef('monster', '5차 유리식', '1/(x^4+x^3+x^2+x+1)', 'sqrt(10+2*sqrt(5))*pi/5',
  { lo: '-inf', hi: 'inf',
  hints: ['분모는 $\\dfrac{x^{5}-1}{x-1}$ 이므로 근이 $1$ 이 아닌 5차 단위근이다.',
          '유수(residue)를 쓰거나, $\\int_{-\\infty}^{\\infty}\\dfrac{dx}{x^{2}-2x\\cos\\theta+1}=\\dfrac{\\pi}{\\sin\\theta}$ 를 두 번 쓴다.'],
  steps: ['$x^{4}+x^{3}+x^{2}+x+1=\\prod\\left(x^{2}-2x\\cos\\dfrac{2k\\pi}{5}+1\\right)$',
          '각 이차식 적분에 위 공식을 적용해 더한다'] });

addDef('monster', '파인만 기법', 'ln(1+1/x^2)', 'pi', { lo: '0', hi: 'inf',
  hints: ['$dv=dx$ 로 부분적분하면 $\\int_{0}^{\\infty}\\dfrac{2\\,dx}{1+x^{2}}$ 가 남는다.',
          '경계항 $x\\ln\\left(1+\\frac{1}{x^{2}}\\right)$ 는 양 끝에서 $0$ 이다.'],
  steps: ['$=\\left[x\\ln\\left(1+\\dfrac{1}{x^{2}}\\right)\\right]_{0}^{\\infty}+2\\int_{0}^{\\infty}\\dfrac{dx}{1+x^{2}}$',
          '$=0+2\\cdot\\dfrac\\pi2=\\pi$'] });

addDef('monster', '지수 치환', 'sqrt(e^x-1)/(2*cosh(x)-1)', 'pi/sqrt(3)', { lo: '0', hi: 'inf',
  hints: ['$u=\\sqrt{e^{x}-1}$ 로 두면 $e^{x}=u^{2}+1$, $dx=\\dfrac{2u\\,du}{u^{2}+1}$ 다.',
          '$2\\cosh x-1=e^{x}+e^{-x}-1=\\dfrac{u^{4}+u^{2}+1}{u^{2}+1}$'],
  steps: ['치환하면 $\\int_{0}^{\\infty}\\dfrac{2u^{2}}{u^{4}+u^{2}+1}du$',
          '$u\\to\\frac1u$ 대칭으로 $\\int_{0}^{\\infty}\\dfrac{u^{2}+1}{u^{4}+u^{2}+1}du$ 를 만든다',
          '$=\\dfrac{\\pi}{\\sqrt3}$'] });

addDef('monster', '적분대회 결승', 'ln(2*e^x-1)/(e^x-1)', 'pi^2/4', { lo: '0', hi: 'inf',
  hints: ['$t=1-e^{-x}$ 로 두면 $\\dfrac{dx}{e^{x}-1}=\\dfrac{dt}{t}\\cdot\\dfrac{1}{1}$ 꼴이 나온다.',
          '$2e^{x}-1=\\dfrac{1+t}{1-t}$ 로 정리된다.'],
  steps: ['$t=1-e^{-x}$ 치환',
          '$\\int_{0}^{1}\\dfrac{1}{t}\\ln\\dfrac{1+t}{1-t}dt=2\\sum_{n\\ge0}\\dfrac{1}{(2n+1)^{2}}$',
          '$=2\\cdot\\dfrac{\\pi^{2}}{8}=\\dfrac{\\pi^{2}}{4}$'] });

addDef('monster', 'Ahmed 적분', 'arctan(sqrt(2+x^2))/((1+x^2)*sqrt(2+x^2))', '5*pi^2/96',
  { lo: '0', hi: '1',
  hints: ['유명한 Ahmed 적분이다. $I(a)=\\int_{0}^{1}\\dfrac{\\arctan(a\\sqrt{2+x^{2}})}{(1+x^{2})\\sqrt{2+x^{2}}}dx$ 로 두고 미분한다.',
          '$a=1$ 에서의 값과 $a\\to\\infty$ 극한을 이어 붙인다.'],
  steps: ['$I\'(a)$ 를 계산하면 유리함수 적분이 된다',
          '$a\\to\\infty$ 에서 $\\dfrac\\pi2\\int_{0}^{1}\\dfrac{dx}{(1+x^{2})\\sqrt{2+x^{2}}}$ 를 얻는다',
          '차를 취하면 $\\dfrac{5\\pi^{2}}{96}$'] });

addDef('monster', 'Ahmed 적분', 'arctan(sqrt(2+x^2))/((1+x^2)*sqrt(2+x^2))', 'pi^2/32',
  { lo: '1', hi: 'inf',
  hints: ['$[0,1]$ 짝과 합치면 $\\int_{0}^{\\infty}$ 가 되어 계산이 쉬워진다.',
          '$\\int_{0}^{\\infty}\\dfrac{\\arctan\\sqrt{2+x^{2}}}{(1+x^{2})\\sqrt{2+x^{2}}}dx=\\dfrac{\\pi^{2}}{6}\\cdot\\dfrac{?}{}$ 를 먼저 구한다.'],
  steps: ['$x\\to\\frac1x$ 대칭은 여기서 통하지 않으므로 $[0,\\infty)$ 값을 직접 구한다',
          '$[0,1]$ 조각 $\\dfrac{5\\pi^{2}}{96}$ 을 빼면 $\\dfrac{\\pi^{2}}{32}$'] });

addDef('monster', '쌍곡선 급수', 'sin(x)*cos(x)/(sinh(x)*cosh(x))', 'pi*tanh(pi/2)/4',
  { lo: '0', hi: 'inf',
  hints: ['$\\dfrac{\\sin x\\cos x}{\\sinh x\\cosh x}=\\dfrac{\\sin 2x}{\\sinh 2x}$ 로 줄인다.',
          '$\\dfrac{1}{\\sinh t}=2\\sum_{n\\ge0}e^{-(2n+1)t}$ 로 펴고 항별로 적분한다.'],
  steps: ['$u=2x$ 로 두면 $\\dfrac12\\int_{0}^{\\infty}\\dfrac{\\sin u}{\\sinh u}du$',
          '급수를 넣으면 $\\sum_{n\\ge0}\\dfrac{1}{(2n+1)^{2}+1}$ 꼴이 된다',
          '$=\\dfrac{\\pi}{4}\\tanh\\dfrac\\pi2$'] });

addDef('monster', '베타 함수', 'sqrt(x/(1-x))*ln(x/(1-x))', 'pi', { lo: '0', hi: '1',
  hints: ['$B(a,b)=\\int_{0}^{1}x^{a-1}(1-x)^{b-1}dx$ 를 $a$ 로 미분해 $\\ln$ 을 만든다.',
          '$a=\\frac32,\;b=\\frac12$ 근처에서 미분값을 본다.'],
  steps: ['$I=\\left.\\dfrac{\\partial}{\\partial s}\\int_{0}^{1}x^{1/2+s}(1-x)^{-1/2-s}dx\\right|_{s=0}$',
          '베타 함수의 $\\psi$ 표현을 쓰면 $\\pi$ 가 나온다'] });

addDef('monster', '위장된 미분', 'e^(cos(2*x))*sin(x+sin(2*x))/sin(x)', 'pi*e/2',
  { lo: '0', hi: 'pi/2',
  hints: ['$\\sin(x+\\sin 2x)=\\sin x\\cos(\\sin 2x)+\\cos x\\sin(\\sin 2x)$ 로 편다.',
          '$e^{\\cos 2x}\\cos(\\sin 2x)$ 는 $\\mathrm{Re}\\,e^{e^{2ix}}$ 의 실수부다.'],
  steps: ['복소수로 $\\mathrm{Re}\\,e^{e^{2ix}}$ 를 급수로 편다',
          '$\\int_{0}^{\\pi/2}$ 에서 상수항만 살아남는다', '$=\\dfrac{\\pi e}{2}$'] });

addDef('monster', '적분대회 고전', 'sqrt(tan(x)*(1-tan(x)))', 'pi*(sqrt((sqrt(2)+1)/2)-1)',
  { lo: '0', hi: 'pi/4',
  hints: ['$u=\\tan x$ 로 두면 $\\int_{0}^{1}\\dfrac{\\sqrt{u(1-u)}}{1+u^{2}}du$ 다.',
          '$u=\\dfrac{1+\\sin\\theta}{2}$ 같은 치환으로 근호를 없앤다.'],
  steps: ['$u=\\tan x$ 치환', '근호를 없애면 유리 삼각적분이 된다',
          '$1+u^{2}$ 의 복소 인수분해로 정리하면 답의 중첩 근호가 나온다'] });

addDef('monster', '급수 전개', 'arctan(x)*ln(x)/x', '-pi^3/32', { lo: '0', hi: '1',
  hints: ['$\\arctan x=\\sum_{n\\ge0}\\dfrac{(-1)^{n}x^{2n+1}}{2n+1}$ 로 펴고 항별로 적분한다.',
          '$\\int_{0}^{1}x^{2n}\\ln x\\,dx=-\\dfrac{1}{(2n+1)^{2}}$'],
  steps: ['$-\\sum_{n\\ge0}\\dfrac{(-1)^{n}}{(2n+1)^{3}}$ 가 된다',
          '이 교대급수는 $\\dfrac{\\pi^{3}}{32}$ 다'] });

addDef('monster', '직교성', 'sin(x)^2020*sin(2022*x)', '1/2021', { lo: '0', hi: 'pi/2',
  hints: ['$\\int_{0}^{\\pi/2}\\sin^{n}x\\sin((n+2)x)dx=\\dfrac{1}{n+1}$ 이라는 점화 구조를 찾는다.',
          '$\\sin((n+2)x)=\\sin(nx)\\cos 2x+\\cos(nx)\\sin 2x$ 로 펴고 부분적분한다.'],
  steps: ['$I_{n}=\\int_{0}^{\\pi/2}\\sin^{n}x\\sin((n+2)x)dx$ 로 두고 점화식을 세운다',
          '$I_{n}=\\dfrac{1}{n+1}$ 이므로 $n=2020$ 에서 $\\dfrac{1}{2021}$'] });

addDef('monster', '직교성', 'cos(x)^2022*cos(2022*x)', 'pi/2^2023', { lo: '0', hi: 'pi/2',
  hints: ['$\\cos^{n}x\\cos(nx)$ 는 $\\left(\\dfrac{e^{ix}+e^{-ix}}{2}\\right)^{n}$ 전개에서 상수항만 남는다.',
          '$\\int_{0}^{\\pi/2}\\cos^{n}x\\cos(nx)dx=\\dfrac{\\pi}{2^{n+1}}$'],
  steps: ['복소지수로 펴면 $\\mathrm{Re}\\left(\\dfrac{(1+e^{2ix})^{n}}{2^{n}}\\right)$ 꼴',
          '이항전개에서 진동하지 않는 항만 살아남는다', '$n=2022$ 에서 $\\dfrac{\\pi}{2^{2023}}$'] });

addDef('monster', '파인만 기법', '(x-sin(x))/(x^3*(x^2+4))', 'pi*(1-e^(-2))/32',
  { lo: '0', hi: 'inf',
  hints: ['$\\dfrac{1}{x^{3}(x^{2}+4)}=\\dfrac{1}{4x^{3}}-\\dfrac{1}{16x}+\\dfrac{x}{16(x^{2}+4)}$ 로 쪼갠다.',
          '$\\int_{0}^{\\infty}\\dfrac{x-\\sin x}{x^{3}}dx=\\dfrac\\pi4$ 와 라플라스 변환을 함께 쓴다.'],
  steps: ['부분분수로 나눈 뒤 각 조각을 디리클레 적분으로 처리한다',
          '$\\int_{0}^{\\infty}\\dfrac{\\sin x}{x(x^{2}+4)}dx$ 에서 $e^{-2}$ 가 나온다'] });

addDef('monster', '함정 문제', '(2*x^3-3*x^2-x+1)^(1/3)', '0', { lo: '0', hi: '1',
  hints: ['$x\\to 1-x$ 를 넣어 보면 피적분함수의 부호가 뒤집힌다.',
          '$2(1-x)^{3}-3(1-x)^{2}-(1-x)+1$ 을 전개해 확인해 보라.'],
  steps: ['$f(1-x)=-f(x)$ 임을 보인다',
          '$I=\\int_{0}^{1}f=\\int_{0}^{1}f(1-x)dx=-I$', '따라서 $I=0$'] });

addDef('monster', '괴상한 근호', 'tan(x)^(1/3)', '(pi*sqrt(3)-ln(8))/6', { lo: '0', hi: 'pi/4',
  hints: ['$u=\\tan^{1/3}x$ 로 두면 $dx=\\dfrac{3u^{2}du}{1+u^{6}}$ 다.',
          '$\\int_{0}^{1}\\dfrac{3u^{3}}{1+u^{6}}du$ 를 $u^{2}$ 로 다시 치환한다.'],
  steps: ['$u=\\tan^{1/3}x$', '$t=u^{2}$ 로 두면 $\\dfrac32\\int_{0}^{1}\\dfrac{t\\,dt}{1+t^{3}}$',
          '부분분수로 풀면 $\\dfrac{\\pi\\sqrt3-\\ln 8}{6}$'] });

addDef('monster', '로그 적분', 'sin(x)*ln(sin(x))/sqrt(1+sin(x)^2)', 'pi*ln(1/2)/8',
  { lo: '0', hi: 'pi/2',
  hints: ['$u=\\cos x$ 로 두면 $\\int_{0}^{1}\\dfrac{\\ln\\sqrt{1-u^{2}}}{\\sqrt{2-u^{2}}}du$ 가 된다.',
          '$\\ln\\sqrt{1-u^{2}}=\\frac12[\\ln(1-u)+\\ln(1+u)]$ 로 쪼갠다.'],
  steps: ['$u=\\cos x$ 치환', '$u=\\sqrt2\\sin\\theta$ 로 한 번 더 치환한다',
          '남는 로그 적분에서 $\\dfrac{\\pi\\ln 2}{8}$ 이 나온다'] });

// ================================================================== 정적분 2차분

addDef('hard', '역수 대칭', 'x/(x^8+2*x^4+1)', 'pi/8', { lo: '0', hi: 'inf',
  hints: ['분모는 $(x^{4}+1)^{2}$ 이다. $u=x^{2}$ 로 두면 차수가 절반이 된다.',
          '$\\dfrac12\\int_{0}^{\\infty}\\dfrac{du}{(u^{2}+1)^{2}}$ 는 표준 점화식이다.'],
  steps: ['$u=x^{2},\;du=2x\\,dx$',
          '$\\dfrac12\\left[\\dfrac{u}{2(u^{2}+1)}+\\dfrac{\\arctan u}{2}\\right]_{0}^{\\infty}=\\dfrac{\\pi}{8}$'] });

addDef('hard', '부분적분', 'ln(1+x^2)/(1+x^2)^3', 'pi*(12*ln(2)-7)/32', { lo: '0', hi: 'inf',
  hints: ['$x=\\tan\\theta$ 로 두면 $\\int_{0}^{\\pi/2}\\cos^{4}\\theta\\ln(\\sec^{2}\\theta)d\\theta$ 다.',
          '$-2\\int_{0}^{\\pi/2}\\cos^{4}\\theta\\ln\\cos\\theta\\,d\\theta$ 를 왈리스 적분의 매개변수 미분으로 얻는다.'],
  steps: ['$x=\\tan\\theta$ 치환',
          '$\\int_{0}^{\\pi/2}\\cos^{s}\\theta\\,d\\theta$ 를 $s$ 로 미분해 $\\ln\\cos$ 를 만든다',
          '$s=4$ 에서 값을 읽으면 $\\dfrac{\\pi(12\\ln 2-7)}{32}$'] });

addDef('hard', '부분적분', 'x^3*ln(x)/(1+x^2)^2', 'ln(2)/4-pi^2/48', { lo: '0', hi: '1',
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac14\\int_{0}^{1}\\dfrac{u\\ln u}{(1+u)^{2}}du$ 다.',
          '$\\dfrac{u}{(1+u)^{2}}=\\dfrac{1}{1+u}-\\dfrac{1}{(1+u)^{2}}$ 로 쪼갠다.'],
  steps: ['$u=x^{2}$ 치환 (로그에서 $\\ln x=\\frac12\\ln u$)',
          '각 조각을 부분적분하면 $\\int_{0}^{1}\\dfrac{\\ln u}{1+u}du=-\\dfrac{\\pi^{2}}{12}$ 가 나온다'] });

addDef('hard', '급수 전개', 'x*e^(-2*x)/(e^(-x)+1)', '1-pi^2/12', { lo: '0', hi: 'inf',
  hints: ['$\\dfrac{e^{-2x}}{e^{-x}+1}=\\dfrac{e^{-x}}{1+e^{x}}$ 로 정리한다.',
          '$\\dfrac{1}{1+e^{x}}=\\sum_{n\\ge1}(-1)^{n-1}e^{-nx}$ 로 펴서 항별로 적분한다.'],
  steps: ['$\\sum_{n\\ge1}(-1)^{n-1}\\int_{0}^{\\infty}xe^{-(n+1)x}dx=\\sum_{n\\ge1}\\dfrac{(-1)^{n-1}}{(n+1)^{2}}$',
          '$=1-\\dfrac{\\pi^{2}}{12}$'] });

addDef('hard', '분수 지수', 'sec(x)^2/(sec(x)+tan(x))^(5/2)', '(30-8*3^(1/4))/63',
  { lo: '0', hi: 'pi/6',
  hints: ['$u=\\sec x+\\tan x$ 로 두면 $du=u\\sec x\\,dx$ 다.',
          '$\\sec x=\\dfrac{u^{2}+1}{2u}$ 이므로 $u$ 만의 거듭제곱 적분이 된다.'],
  steps: ['$u=\\sec x+\\tan x$', '$\\int\\dfrac{u^{2}+1}{2}u^{-7/2}du$ 꼴로 바뀐다',
          '항별로 적분한 뒤 $u(0)=1,\;u(\\pi/6)=\\sqrt3$ 을 대입한다'] });

addDef('hard', '유명한 근사', 'x^4*(1+x)^4/(1+x^2)', '94/21-pi', { lo: '0', hi: '1',
  hints: ['$x^{4}(1+x)^{4}$ 를 전개해 $1+x^{2}$ 로 나눈다.',
          '$\\dfrac{22}{7}-\\pi$ 문제의 짝 — 이번에는 $\\dfrac{94}{21}$ 이 나온다.'],
  steps: ['나눗셈하면 $x^{6}+4x^{5}+5x^{4}-4x^{2}+4-\\dfrac{4}{1+x^{2}}$',
          '$\\dfrac17+\\dfrac23+1-\\dfrac43+4-\\pi=\\dfrac{94}{21}-\\pi$'] });

addDef('monster', '적분대회 결승', 'tan(x)^(1/3)/(sin(x)+cos(x))^2', '2*sqrt(3)*pi/9',
  { lo: '0', hi: 'pi/2',
  hints: ['분모·분자를 $\\cos^{2}x$ 로 나누면 $\\dfrac{u^{1/3}\\,du}{(1+u)^{2}}$ 꼴이 된다 ($u=\\tan x$).',
          '$\\int_{0}^{\\infty}\\dfrac{u^{s-1}}{(1+u)^{2}}du=\\dfrac{\\pi(s-1)}{\\sin\\pi s}$ 를 쓴다.'],
  steps: ['$u=\\tan x$ 로 두면 $\\int_{0}^{\\infty}\\dfrac{u^{1/3}}{(1+u)^{2}}du$',
          '베타 함수 $B\\left(\\dfrac43,\\dfrac23\\right)$ 로 읽는다',
          '$=\\dfrac{2\\sqrt3\\pi}{9}$'] });

addDef('monster', '이중 로그', 'ln((1-sqrt(2)*x+x^2)/(1-sqrt(3)*x+x^2))/x', '19*pi^2/288',
  { lo: '0', hi: '1',
  hints: ['$\\int_{0}^{1}\\dfrac{\\ln(1-2x\\cos\\theta+x^{2})}{x}dx=\\dfrac{\\theta^{2}}{2}-\\dfrac{\\pi\\theta}{2}+\\dfrac{\\pi^{2}}{6}$ 를 쓴다.',
          '$\\sqrt2=2\\cos\\dfrac\\pi4$, $\\sqrt3=2\\cos\\dfrac\\pi6$ 이다.'],
  steps: ['두 로그를 각각 위 공식에 넣는다',
          '$\\theta=\\dfrac\\pi4$ 와 $\\theta=\\dfrac\\pi6$ 의 차를 취한다',
          '$=\\dfrac{19\\pi^{2}}{288}$'] });

addDef('monster', '로그 적분', 'x*ln(sin(x))/sin(2*x)', '-pi^3/48', { lo: '0', hi: 'pi/2',
  hints: ['$\\sin 2x=2\\sin x\\cos x$ 이므로 $\\dfrac{x\\ln\\sin x}{2\\sin x\\cos x}$ 다.',
          '$x\\to\\dfrac\\pi2-x$ 대칭으로 $\\ln\\sin$ 과 $\\ln\\cos$ 를 짝지어 본다.'],
  steps: ['대칭 치환으로 $I$ 를 다시 쓴 뒤 원래 식과 더한다',
          '$\\ln\\sin x+\\ln\\cos x=\\ln\\dfrac{\\sin 2x}{2}$ 를 이용한다',
          '$=-\\dfrac{\\pi^{3}}{48}$'] });

addDef('monster', '푸아송 합', 'cos(2*pi*x^2)/cosh(pi*x)^2', '1/4', { lo: '0', hi: 'inf',
  hints: ['$\\operatorname{sech}^{2}$ 와 $\\cos(2\\pi x^{2})$ 는 둘 다 푸리에 변환의 고정점 근처에 있다.',
          '$e^{-\\pi x^{2}}$ 가 자기 자신의 푸리에 변환이라는 점에서 출발한다.'],
  steps: ['$\\cos(2\\pi x^{2})=\\mathrm{Re}\\,e^{2\\pi i x^{2}}$ 로 놓는다',
          '푸아송 합공식을 $\\operatorname{sech}^{2}$ 에 적용한다', '$=\\dfrac14$'] });

addDef('monster', '역수 대칭', 'ln(x)/((pi^2+ln(x)^2)*(1+x)^2*sqrt(x))', '-pi/24',
  { lo: '0', hi: 'inf',
  hints: ['$x\\to\\dfrac1x$ 로 두면 $\\ln x$ 의 부호만 뒤집힌다 — 대칭을 쓴다.',
          '$\\pi^{2}+\\ln^{2}x$ 는 $\\ln(-x)$ 의 절댓값 제곱이므로 복소 로그를 부른다.'],
  steps: ['$x\\to1/x$ 대칭으로 구간을 $[0,1]$ 로 접는다',
          '$\\dfrac{1}{\\pi^{2}+\\ln^{2}x}$ 를 라플라스 표현으로 바꾼다', '$=-\\dfrac{\\pi}{24}$'] });

addDef('monster', '위장된 급수', 'sin(2*x)*sec(x)^4/(e^(2*pi*tan(x))-1)', '1/12',
  { lo: '0', hi: 'pi/2',
  hints: ['$u=\\tan x$ 로 두면 $\\int_{0}^{\\infty}\\dfrac{2u\\,du}{e^{2\\pi u}-1}$ 가 된다.',
          '$\\int_{0}^{\\infty}\\dfrac{u\\,du}{e^{2\\pi u}-1}=\\dfrac{1}{24}$ (베르누이 수)'],
  steps: ['$\\sin 2x\\sec^{4}x=2\\tan x\\sec^{2}x$ 이므로 $u=\\tan x$ 치환이 딱 맞는다',
          '$2\\int_{0}^{\\infty}\\dfrac{u}{e^{2\\pi u}-1}du=2\\cdot\\dfrac{1}{24}=\\dfrac1{12}$'] });

addDef('monster', '역함수 대칭', 'arctan(cot(x)^2)', '(pi^2-2*ln(sqrt(2)+1)^2)/8',
  { lo: '0', hi: 'pi/4',
  hints: ['$\\arctan(\\cot^{2}x)=\\dfrac\\pi2-\\arctan(\\tan^{2}x)$ 로 바꾼다.',
          '$\\int_{0}^{\\pi/4}\\arctan(\\tan^{2}x)dx$ 를 파인만 기법으로 계산한다.'],
  steps: ['$I(a)=\\int_{0}^{\\pi/4}\\arctan(a\\tan^{2}x)dx$ 로 두고 $a$ 로 미분한다',
          '$I\'(a)$ 는 유리 삼각적분이 된다', '$a=1$ 까지 적분하면 $\\ln^{2}(\\sqrt2+1)$ 항이 나온다'] });

addDef('monster', '역수 대칭', 'x*ln(x)/(x^8+2*x^4+1)', '-pi/16', { lo: '0', hi: 'inf',
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac14\\int_{0}^{\\infty}\\dfrac{\\ln u}{(u^{2}+1)^{2}}du$ 다.',
          '$\\int_{0}^{\\infty}\\dfrac{\\ln u}{(u^{2}+1)^{2}}du=-\\dfrac\\pi4$'],
  steps: ['$u=x^{2}$ 치환',
          '$u\\to1/u$ 대칭으로 $\\ln u$ 항을 정리한다', '$=-\\dfrac{\\pi}{16}$'] });

addDef('monster', '역수 대칭', 'x^5*ln(x)/(x^8+2*x^4+1)', 'pi/16', { lo: '0', hi: 'inf',
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac14\\int_{0}^{\\infty}\\dfrac{u^{2}\\ln u}{(u^{2}+1)^{2}}du$ 다.',
          '$u\\to\\dfrac1u$ 로 두면 앞 문제와 부호만 반대가 된다.'],
  steps: ['$u=x^{2}$ 치환', '$u\\to1/u$ 대칭으로 앞 문제와 짝을 짓는다', '$=\\dfrac{\\pi}{16}$'] });

addDef('monster', '로그 제곱', 'ln(x)^2/(x^2+2*x+2)', '(5*pi^3+4*pi*ln(2)^2)/64',
  { lo: '0', hi: 'inf',
  hints: ['$x^{2}+2x+2=(x+1)^{2}+1$ 이므로 극이 $-1\\pm i$ 다.',
          '$\\int_{0}^{\\infty}\\dfrac{\\ln^{2}x}{x^{2}+2x+2}dx$ 는 열쇠구멍 경로(keyhole)로 푼다.'],
  steps: ['$\\oint\\dfrac{\\ln^{3}z}{z^{2}+2z+2}dz$ 를 열쇠구멍 경로로 계산한다',
          '유수는 $z=-1\\pm i$ 에서 나온다',
          '실수부를 읽으면 $\\dfrac{5\\pi^{3}+4\\pi\\ln^{2}2}{64}$'] });

addDef('monster', '파인만 기법', 'arctan(2*cos(x)^2)/cos(x)^2', 'sqrt((sqrt(5)-1)/2)*pi',
  { lo: '0', hi: 'pi/2',
  hints: ['$I(a)=\\int_{0}^{\\pi/2}\\dfrac{\\arctan(a\\cos^{2}x)}{\\cos^{2}x}dx$ 로 두고 $a$ 로 미분한다.',
          '$I\'(a)=\\int_{0}^{\\pi/2}\\dfrac{dx}{1+a^{2}\\cos^{4}x}$ 는 $u=\\tan x$ 로 풀린다.'],
  steps: ['$I\'(a)$ 를 계산하면 $\\dfrac{\\pi}{\\sqrt2}\\cdot\\dfrac{1}{\\sqrt{1+\\sqrt{1+a^{2}}}}$ 꼴이 된다',
          '$a=0$ 에서 $2$ 까지 적분한다', '황금비가 등장해 $\\sqrt{\\dfrac{\\sqrt5-1}{2}}\\pi$ 가 나온다'] });

addDef('monster', '대칭 논법', '(pi-4*x)*tan(x)/(1-tan(x))', 'pi*ln(2)-pi^2/4',
  { lo: '-pi/4', hi: 'pi/4',
  hints: ['$x\\to-x$ 로 두고 원래 식과 더하면 홀수 부분이 상쇄된다.',
          '$\\dfrac{\\tan x}{1-\\tan x}+\\dfrac{-\\tan x}{1+\\tan x}$ 를 정리해 보라.'],
  steps: ['$x\\to-x$ 대칭으로 $2I$ 를 만든다',
          '$\\tan\\left(\\dfrac\\pi4-x\\right)=\\dfrac{1-\\tan x}{1+\\tan x}$ 를 쓴다',
          '$\\int_{0}^{\\pi/4}\\ln(1+\\tan x)dx=\\dfrac{\\pi\\ln 2}{8}$ 로 귀결된다'] });

addDef('monster', '괴상한 겉모습', 'x^2*sech((x^4-10*x^2+6*x+7)/(x^3-7*x+6))',
    'pi^3/4+3*pi', { lo: '-inf', hi: 'inf',
  hints: ['지수의 유리식을 부분분수로 쪼개 보라. $x^{3}-7x+6=(x-1)(x-2)(x+3)$ 이다.',
          '글래서 주인공 정리(Glasser master theorem): $\\int_{\\mathbb R}f\\left(x-\\sum\\frac{a_{k}}{x-b_{k}}\\right)dx=\\int_{\\mathbb R}f(x)dx$'],
  steps: ['지수가 $x-\\dfrac{a_{1}}{x-1}-\\dfrac{a_{2}}{x-2}-\\dfrac{a_{3}}{x+3}$ 꼴임을 확인한다',
          '글래서 정리로 $\\int_{\\mathbb R}x^{2}\\operatorname{sech}x\\,dx$ 로 바뀐다 (보정항 포함)',
          '$=\\dfrac{\\pi^{3}}{4}+3\\pi$'] });


// ================================================================== MIT 적분 벌 예선 (2010~2023)
//
//   MIT Integration Bee 예선 문제들. 문제 자체는 MIT 가 공개한 것이고,
//   힌트와 풀이는 여기서 새로 썼다. 기준 부정적분·정적분 값은 전부
//   아래 검증 단계에서 수치로 확인한다.
//
//   전체 280문항 중 259문항을 옮겼다. 빠진 21문항과 이유:
//     바닥·천장함수      2012#7, 2013#14, 2014#18, 2016#8, 2022#3, 2023#8
//     중첩 절댓값        2023#11
//     극한 문제(적분 아님) 2017#15, 2019#12, 2022#11
//     음수의 홀수 거듭제곱근 (파서가 NaN)  2014#2, 2016#7
//     진동이 너무 빨라 수치적분 불가  2018#3, 2019#6
//     이항계수가 천문학적  2020#9
//     급수·무한곱 형태     2020#14, 2022#17(→1-x 로 중복), 2023#17(→1-x 로 중복)
//     피적분함수가 항등적으로 0 (부정적분 채점 불가)  2023#10
//     정리하면 x 하나뿐  2020#6

// --- 2010 -----------------------------------------------------------

addDef('hard', '곱-합 공식', 'sin(x)*sin(2*x)*sin(3*x)', '1/6',
  { lo: '0', hi: 'pi/2',
  hints: ['$\\sin x\\sin 3x$ 를 먼저 합으로 바꾼다.',
          '남은 $\\sin 2x$ 를 곱하면 $\\sin 2x,\\sin 4x,\\sin 6x$ 만 남는다.'],
  steps: ['$\\sin x\\sin3x=\\dfrac{\\cos2x-\\cos4x}{2}$',
          '정리하면 피적분함수는 $\\dfrac{\\sin2x+\\sin4x-\\sin6x}{4}$',
          '$=\\dfrac{1}{4}\\left(1+0-\\dfrac13\\right)=\\dfrac16$'] });

addDef('hard', '삼각 치환', 'sin(2*x)^3*cos(x)', '16/35',
  { lo: '0', hi: 'pi/2',
  hints: ['$\\sin 2x=2\\sin x\\cos x$ 를 먼저 풀어 쓴다.',
          '$8\\sin^{3}x\\cos^{4}x$ 가 되면 $u=\\cos x$ 로 끝난다.'],
  steps: ['$\\sin^{3}2x\\cos x=8\\sin^{3}x\\cos^{4}x$',
          '$u=\\cos x$ 로 두면 $8\\int_{0}^{1}(1-u^{2})u^{4}du$',
          '$=8\\left(\\dfrac15-\\dfrac17\\right)=\\dfrac{16}{35}$'] });

add('hard', '치환적분', '(x+1)^2*(x-1)^(1/3)',
    '(3/10)*(x-1)^(10/3)+(12/7)*(x-1)^(7/3)+3*(x-1)^(4/3)',
  { domain: [1.2, 3.0],
  hints: ['$u=x-1$ 로 두면 $x+1=u+2$ 가 된다.',
          '$(u+2)^{2}u^{1/3}$ 을 전개하면 거듭제곱 세 개다.'],
  steps: ['$u=x-1$ 치환',
          '$(u^{2}+4u+4)u^{1/3}=u^{7/3}+4u^{4/3}+4u^{1/3}$',
          '항마다 거듭제곱 법칙을 쓴다'] });

add('hard', '부분적분', 'x*ln(1+1/x)',
    'x^2*ln(1+1/x)/2+x/2-ln(x+1)/2',
  { domain: [0.4, 3.0],
  hints: ['$\\ln\\left(1+\\dfrac1x\\right)=\\ln(x+1)-\\ln x$ 로 쪼개면 미분이 쉽다.',
          '그 도함수는 $-\\dfrac{1}{x(x+1)}$ 이다.'],
  steps: ['$u=\\ln(1+1/x),\\ dv=x\\,dx$ 로 부분적분',
          '$\\dfrac{x^{2}}{2}\\ln\\left(1+\\dfrac1x\\right)+\\dfrac12\\int\\dfrac{x}{x+1}dx$',
          '$=\\dfrac{x^{2}}{2}\\ln\\left(1+\\dfrac1x\\right)+\\dfrac{x}{2}-\\dfrac{\\ln(x+1)}{2}$'] });

addDef('hard', '로그 치환', 'sin(ln(x))^2', '2/5',
  { lo: '0', hi: '1',
  hints: ['$t=\\ln x$ 로 두면 구간이 $(-\\infty,0]$ 이 되고 $dx=e^{t}dt$ 다.',
          '$\\sin^{2}t=\\dfrac{1-\\cos2t}{2}$ 로 낮춘다.'],
  steps: ['$t=\\ln x$ 치환 $\\Rightarrow\\int_{-\\infty}^{0}\\sin^{2}t\\,e^{t}dt$',
          '$\\int_{-\\infty}^{0}e^{t}dt=1,\\ \\int_{-\\infty}^{0}e^{t}\\cos2t\\,dt=\\dfrac15$',
          '$=\\dfrac{1}{2}\\left(1-\\dfrac15\\right)=\\dfrac25$'] });

add('medium', '지수 유리식', '1/(1+3*e^x)', 'x-ln(1+3*e^x)',
  { domain: [-1.0, 2.0],
  hints: ['$\\dfrac{1}{1+3e^{x}}=1-\\dfrac{3e^{x}}{1+3e^{x}}$ 로 쪼갠다.',
          '뒤쪽은 분모의 도함수가 분자다.'],
  steps: ['$1-\\dfrac{3e^{x}}{1+3e^{x}}$ 로 나눈다',
          '뒤 항은 $\\ln(1+3e^{x})$',
          '$=x-\\ln(1+3e^{x})$'] });

addDef('monster', '탄젠트 치환', '1/(sin(x)^3*cos(x)^5)', '16/3+3*ln(3)/2',
  { lo: 'pi/4', hi: 'pi/3',
  hints: ['$t=\\tan x$ 로 두면 $\\sin^{3}x\\cos^{5}x=\\dfrac{t^{3}}{(1+t^{2})^{4}}$ 다.',
          '$dx=\\dfrac{dt}{1+t^{2}}$ 를 곱하면 $\\dfrac{(1+t^{2})^{3}}{t^{3}}$ 만 남는다.'],
  steps: ['$t=\\tan x$ 치환 $\\Rightarrow\\displaystyle\\int_{1}^{\\sqrt3}\\dfrac{(1+t^{2})^{3}}{t^{3}}dt$',
          '전개하면 $t^{-3}+3t^{-1}+3t+t^{3}$',
          '$\\left[-\\dfrac{1}{2t^{2}}+3\\ln t+\\dfrac{3t^{2}}{2}+\\dfrac{t^{4}}{4}\\right]_{1}^{\\sqrt3}=\\dfrac{16}{3}+\\dfrac{3\\ln3}{2}$'] });

addDef('hard', '역삼각 치환', '1/(x*sqrt(x^4-1))', 'pi/4',
  { lo: '1', hi: 'inf',
  hints: ['분자·분모에 $x$ 를 곱해 $u=x^{2}$ 를 만든다.',
          '$\\int\\dfrac{du}{u\\sqrt{u^{2}-1}}=\\operatorname{arcsec}u$ 다.'],
  steps: ['$u=x^{2}\\Rightarrow\\dfrac12\\int_{1}^{\\infty}\\dfrac{du}{u\\sqrt{u^{2}-1}}$',
          '$=\\dfrac12\\left[\\operatorname{arcsec}u\\right]_{1}^{\\infty}$',
          '$=\\dfrac12\\cdot\\dfrac{\\pi}{2}=\\dfrac{\\pi}{4}$'] });

add('hard', '부분분수', '1/(x*(x^5+1))', 'ln(x)-ln(x^5+1)/5',
  { domain: [0.4, 2.4],
  hints: ['$\\dfrac{1}{x(x^{5}+1)}=\\dfrac1x-\\dfrac{x^{4}}{x^{5}+1}$ 이다.',
          '뒤쪽은 분모의 도함수가 $5x^{4}$ 다.'],
  steps: ['$\\dfrac1x-\\dfrac{x^{4}}{x^{5}+1}$ 로 쪼갠다',
          '$=\\ln x-\\dfrac{1}{5}\\ln(x^{5}+1)$'] });

addDef('monster', '분수 지수', 'sqrt(tan(x))', 'pi/(2*sqrt(2))+ln(sqrt(2)-1)/sqrt(2)',
  { lo: '0', hi: 'pi/4',
  hints: ['$u=\\sqrt{\\tan x}$ 로 두면 $dx=\\dfrac{2u\\,du}{1+u^{4}}$ 다.',
          '$\\dfrac{2u^{2}}{1+u^{4}}$ 는 $1+u^{4}=(u^{2}+\\sqrt2u+1)(u^{2}-\\sqrt2u+1)$ 로 쪼갠다.'],
  steps: ['$u=\\sqrt{\\tan x}\\Rightarrow2\\displaystyle\\int_{0}^{1}\\dfrac{u^{2}}{1+u^{4}}du$',
          '$\\dfrac{1}{2\\sqrt2}\\ln\\dfrac{u^{2}-\\sqrt2u+1}{u^{2}+\\sqrt2u+1}+\\dfrac{1}{\\sqrt2}\\left(\\arctan(\\sqrt2u+1)+\\arctan(\\sqrt2u-1)\\right)$ 를 대입',
          '$=\\dfrac{\\pi}{2\\sqrt2}+\\dfrac{\\ln(\\sqrt2-1)}{\\sqrt2}$'] });

addDef('monster', '킹 성질', 'ln(1+x)/(1+x^2)', 'pi*ln(2)/8',
  { lo: '0', hi: '1',
  hints: ['$x=\\tan\\theta$ 로 두면 $\\int_{0}^{\\pi/4}\\ln(1+\\tan\\theta)d\\theta$ 가 된다.',
          '$\\theta\\to\\dfrac\\pi4-\\theta$ 를 넣고 두 식을 더해 보라.'],
  steps: ['$x=\\tan\\theta$ 치환',
          '$\\ln(1+\\tan\\theta)+\\ln\\left(1+\\tan\\left(\\tfrac\\pi4-\\theta\\right)\\right)=\\ln2$',
          '$2I=\\dfrac{\\pi}{4}\\ln2\\Rightarrow I=\\dfrac{\\pi\\ln2}{8}$'] });

addDef('hard', '거듭제곱근 치환', 'sqrt(x)/(sqrt(x)-x^(1/3))', '10747/10+6*ln(2)',
  { lo: '64', hi: '729',
  hints: ['$2$ 와 $3$ 의 최소공배수를 보고 $x=t^{6}$ 으로 둔다.',
          '적분 구간이 $t=2$ 에서 $t=3$ 으로 깔끔해진다.'],
  steps: ['$x=t^{6},\\ dx=6t^{5}dt\\Rightarrow\\displaystyle\\int_{2}^{3}\\dfrac{6t^{6}}{t-1}dt$',
          '$\\dfrac{t^{6}}{t-1}=t^{5}+t^{4}+t^{3}+t^{2}+t+1+\\dfrac{1}{t-1}$',
          '$=\\dfrac{10747}{10}+6\\ln2$'] });

add('monster', '지수 탑', 'x^x*(1+ln(x))', 'x^x',
  { domain: [0.45, 2.2],
  hints: ['$x^{x}=e^{x\\ln x}$ 로 쓰고 미분해 보라.',
          '$(x^{x})\'=x^{x}(1+\\ln x)$ 다.'],
  steps: ['$x^{x}=e^{x\\ln x}$',
          '$(e^{x\\ln x})\'=e^{x\\ln x}(\\ln x+1)$',
          '피적분함수가 그대로 도함수이므로 $=x^{x}$'] });

addDef('hard', '치환적분', 'x^(13/2)*sqrt(1+x^(5/2))', '(88*sqrt(2)-32)/525',
  { lo: '0', hi: '1',
  hints: ['$t=1+x^{5/2}$ 로 두면 $dt=\\dfrac52x^{3/2}dx$ 다.',
          '$x^{13/2}=x^{5}\\cdot x^{3/2}$ 이고 $x^{5}=(t-1)^{2}$ 이다.'],
  steps: ['$t=1+x^{5/2}\\Rightarrow\\dfrac25\\displaystyle\\int_{1}^{2}(t-1)^{2}\\sqrt t\\,dt$',
          '$=\\dfrac25\\int_{1}^{2}\\left(t^{5/2}-2t^{3/2}+t^{1/2}\\right)dt$',
          '$=\\dfrac{88\\sqrt2-32}{525}$'] });

addDef('medium', '삼각 치환', '1/(1+x^2)^2', 'pi/4',
  { lo: '0', hi: 'inf',
  hints: ['$x=\\tan\\theta$ 로 두면 $\\dfrac{dx}{(1+x^{2})^{2}}=\\cos^{2}\\theta\\,d\\theta$ 다.',
          '구간은 $0$ 에서 $\\dfrac\\pi2$ 가 된다.'],
  steps: ['$x=\\tan\\theta$ 치환',
          '$\\int_{0}^{\\pi/2}\\cos^{2}\\theta\\,d\\theta=\\dfrac{\\pi}{4}$'] });

addDef('hard', '부분분수', '1/(x^4-13*x^2+36)', 'ln(3)/20-ln(2)/30',
  { lo: '0', hi: '1',
  hints: ['$x^{4}-13x^{2}+36=(x^{2}-4)(x^{2}-9)$ 이다.',
          '$\\dfrac{1}{(x^{2}-4)(x^{2}-9)}=\\dfrac15\\left(\\dfrac{1}{x^{2}-9}-\\dfrac{1}{x^{2}-4}\\right)$'],
  steps: ['부분분수로 쪼갠다',
          '$\\int\\dfrac{dx}{x^{2}-a^{2}}=\\dfrac{1}{2a}\\ln\\left|\\dfrac{x-a}{x+a}\\right|$',
          '$=\\dfrac{\\ln3}{20}-\\dfrac{\\ln2}{30}$'] });

add('medium', '로그 치환', 'ln(ln(x))/x', 'ln(x)*ln(ln(x))-ln(x)',
  { domain: [1.45, 4.0],
  hints: ['$u=\\ln x$ 로 두면 $\\int\\ln u\\,du$ 가 된다.',
          '$\\int\\ln u\\,du=u\\ln u-u$ 다.'],
  steps: ['$u=\\ln x,\\ du=\\dfrac{dx}{x}$',
          '$\\int\\ln u\\,du=u\\ln u-u$',
          '$=\\ln x\\ln(\\ln x)-\\ln x$'] });

add('hard', '삼각 유리식', '(1+cot(x))/(1-cot(x))', 'ln(sin(x)-cos(x))',
  { domain: [1.0, 2.5], lnAbs: true,
  hints: ['분자·분모에 $\\sin x$ 를 곱하면 $\\dfrac{\\sin x+\\cos x}{\\sin x-\\cos x}$ 다.',
          '분모의 도함수가 정확히 분자다.'],
  steps: ['$\\dfrac{1+\\cot x}{1-\\cot x}=\\dfrac{\\sin x+\\cos x}{\\sin x-\\cos x}$',
          '$u=\\sin x-\\cos x\\Rightarrow du=(\\cos x+\\sin x)dx$',
          '$=\\ln|\\sin x-\\cos x|$'] });

add('monster', '로그 미분 되짚기', '(cos(x)+x*sin(x))/(x*(x+cos(x)))',
    'ln(x/(x+cos(x)))',
  { domain: [1.0, 3.0], lnAbs: true,
  hints: ['답이 $\\ln\\dfrac{f}{g}$ 꼴이라고 짐작하고 미분해 보라.',
          '$\\dfrac1x-\\dfrac{1-\\sin x}{x+\\cos x}$ 를 통분하면 무엇이 되는가?'],
  steps: ['$\\left(\\ln\\dfrac{x}{x+\\cos x}\\right)\'=\\dfrac1x-\\dfrac{1-\\sin x}{x+\\cos x}$',
          '통분하면 $\\dfrac{\\cos x+x\\sin x}{x(x+\\cos x)}$',
          '$=\\ln\\left|\\dfrac{x}{x+\\cos x}\\right|$'] });

addDef('monster', '바이어슈트라스 치환', '1/(sin(x)+sec(x))', 'ln(2+sqrt(3))/sqrt(3)',
  { lo: '0', hi: 'pi/2',
  hints: ['$\\dfrac{1}{\\sin x+\\sec x}=\\dfrac{\\cos x}{1+\\sin x\\cos x}$ 로 고친다.',
          '$s=\\sin x$ 로 두면 $\\displaystyle\\int_{0}^{1}\\dfrac{ds}{1+s\\sqrt{1-s^{2}}}$ 다.'],
  steps: ['$\\dfrac{\\cos x}{1+\\sin x\\cos x}$ 로 정리',
          '유리화하면 $\\dfrac{1-s\\sqrt{1-s^{2}}}{s^{4}-s^{2}+1}$',
          '$s^{4}-s^{2}+1=(s^{2}+\\sqrt3s+1)(s^{2}-\\sqrt3s+1)$ 로 쪼개면 $\\dfrac{\\ln(2+\\sqrt3)}{\\sqrt3}$'] });

addDef('hard', '지수 치환', '1/sqrt(1+e^x+e^(2*x))', 'ln(1+2/sqrt(3))',
  { lo: '0', hi: 'inf',
  hints: ['$u=e^{x}$ 로 두면 $\\displaystyle\\int_{1}^{\\infty}\\dfrac{du}{u\\sqrt{u^{2}+u+1}}$ 다.',
          '$\\int\\dfrac{du}{u\\sqrt{au^{2}+bu+c}}$ 는 $c>0$ 일 때 $u\\to1/u$ 로 풀린다.'],
  steps: ['$u=e^{x}$ 치환',
          '$-\\ln\\dfrac{2+u+2\\sqrt{u^{2}+u+1}}{u}$ 가 원시함수다',
          '$=\\ln\\dfrac{3+2\\sqrt3}{3}=\\ln\\left(1+\\dfrac{2}{\\sqrt3}\\right)$'] });

addDef('medium', '치환 후 부분적분', 'x^3*e^(x^2)', '1/2',
  { lo: '0', hi: '1',
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\int_{0}^{1}ue^{u}du$ 다.',
          '$\\int ue^{u}du=(u-1)e^{u}$'],
  steps: ['$u=x^{2}\\Rightarrow\\dfrac12\\int_{0}^{1}ue^{u}du$',
          '$=\\dfrac12\\left[(u-1)e^{u}\\right]_{0}^{1}=\\dfrac12(0+1)=\\dfrac12$'] });

addDef('monster', '무한 중첩 근호', '(x+sqrt(x^2+4))/2',
    '1/4+sqrt(5)/4+ln((1+sqrt(5))/2)',
  { lo: '0', hi: '1',
  hints: ['$y=\\sqrt{1+x\\sqrt{1+x\\sqrt{\\cdots}}}$ 는 $y^{2}=1+xy$ 를 만족한다.',
          '양수 해는 $y=\\dfrac{x+\\sqrt{x^{2}+4}}{2}$ 다.'],
  steps: ['$y^{2}=1+xy\\Rightarrow y=\\dfrac{x+\\sqrt{x^{2}+4}}{2}$',
          '$\\int\\sqrt{x^{2}+4}\\,dx=\\dfrac{x\\sqrt{x^{2}+4}}{2}+2\\ln\\left(x+\\sqrt{x^{2}+4}\\right)$',
          '$=\\dfrac14+\\dfrac{\\sqrt5}{4}+\\ln\\dfrac{1+\\sqrt5}{2}$'] });

add('hard', '미분 되짚기', '1/ln(x)-1/ln(x)^2', 'x/ln(x)',
  { domain: [1.45, 4.0],
  hints: ['$\\left(\\dfrac{x}{\\ln x}\\right)\'$ 를 계산해 보라.',
          '몫의 미분법으로 $\\dfrac{\\ln x-1}{\\ln^{2}x}$ 가 나온다.'],
  steps: ['$\\left(\\dfrac{x}{\\ln x}\\right)\'=\\dfrac{\\ln x-1}{\\ln^{2}x}$',
          '$=\\dfrac{1}{\\ln x}-\\dfrac{1}{\\ln^{2}x}$',
          '피적분함수와 같으므로 $=\\dfrac{x}{\\ln x}$'] });

addDef('hard', '베타 함수', 'sqrt(x-1)*sqrt(2-x)', 'pi/8',
  { lo: '1', hi: '2',
  hints: ['$x=1+t$ 로 옮기면 $\\int_{0}^{1}\\sqrt{t(1-t)}\\,dt$ 다.',
          '반원의 넓이로 읽어도 되고 $t=\\sin^{2}\\theta$ 로 풀어도 된다.'],
  steps: ['$x=1+t$ 로 평행이동',
          '$\\int_{0}^{1}\\sqrt{t(1-t)}dt$ 는 반지름 $\\dfrac12$ 인 반원의 넓이',
          '$=\\dfrac{\\pi}{8}$'] });


// --- 2011 -----------------------------------------------------------

add('hard', '인수분해', '(x^6-1)/(x^4+x^3-x-1)', 'x^3/3-x^2/2+x',
  { domain: [0.3, 2.4],
  hints: ['분모를 묶어 보라: $x^{3}(x+1)-(x+1)$ 이다.',
          '$x^{6}-1=(x^{3}-1)(x^{3}+1)$ 로 쪼개면 대부분 약분된다.'],
  steps: ['$x^{4}+x^{3}-x-1=(x+1)(x-1)(x^{2}+x+1)$',
          '$x^{6}-1=(x-1)(x^{2}+x+1)(x+1)(x^{2}-x+1)$',
          '약분하면 $x^{2}-x+1$ 만 남는다'] });

add('medium', '부분적분', '2*ln(x)+ln(x)^2', 'x*ln(x)^2',
  { domain: D.pos,
  hints: ['$\\left(x\\ln^{2}x\\right)\'$ 를 곱의 미분법으로 계산해 보라.',
          '$\\ln^{2}x+2\\ln x$ 가 나온다.'],
  steps: ['$\\left(x\\ln^{2}x\\right)\'=\\ln^{2}x+x\\cdot\\dfrac{2\\ln x}{x}$',
          '$=\\ln^{2}x+2\\ln x$',
          '피적분함수와 같으므로 $=x\\ln^{2}x$'] });

add('medium', '치환적분', '2*x/sqrt(1-x^4)', 'asin(x^2)',
  { domain: [0.15, 0.9],
  hints: ['$u=x^{2}$ 로 두면 $du=2x\\,dx$ 다.',
          '$\\int\\dfrac{du}{\\sqrt{1-u^{2}}}=\\arcsin u$'],
  steps: ['$u=x^{2}$ 치환', '$\\int\\dfrac{du}{\\sqrt{1-u^{2}}}=\\arcsin u$', '$=\\arcsin(x^{2})$'] });

add('medium', '다항식 나눗셈', '(x^2+1)/(x+1)', 'x^2/2-x+2*ln(x+1)',
  { domain: D.poly, lnAbs: true,
  hints: ['분자를 분모로 나눠 몫과 나머지를 구한다.',
          '$x^{2}+1=(x+1)(x-1)+2$'],
  steps: ['$\\dfrac{x^{2}+1}{x+1}=x-1+\\dfrac{2}{x+1}$',
          '$=\\dfrac{x^{2}}{2}-x+2\\ln|x+1|$'] });

add('hard', '삼각 유리식', '(sin(x)^3+sin(x)^2-2*sin(x)-2)/(sin(x)^2+2*sin(x)+1)',
    '-cos(x)-x-tan(x)+1/cos(x)',
  { domain: D.trig,
  hints: ['$s=\\sin x$ 로 보고 분자·분모를 인수분해한다.',
          '$\\dfrac{(s+1)(s^{2}-2)}{(s+1)^{2}}=\\dfrac{s^{2}-2}{s+1}=s-1-\\dfrac{1}{s+1}$'],
  steps: ['정리하면 $\\sin x-1-\\dfrac{1}{1+\\sin x}$',
          '$\\int\\dfrac{dx}{1+\\sin x}=\\tan x-\\sec x$',
          '$=-\\cos x-x-\\tan x+\\sec x$'] });

add('medium', '쌍곡선함수', '1/sinh(x)^2', '-cosh(x)/sinh(x)',
  { domain: D.hyp,
  hints: ['$\\operatorname{csch}^{2}x$ 의 원시함수는 $-\\coth x$ 다.',
          '$(\\coth x)\'=-\\operatorname{csch}^{2}x$ 를 확인해 보라.'],
  steps: ['$(\\coth x)\'=\\dfrac{\\sinh^{2}x-\\cosh^{2}x}{\\sinh^{2}x}=-\\dfrac{1}{\\sinh^{2}x}$',
          '$=-\\coth x$'] });

add('medium', '삼각 치환', 'sec(x)^4*tan(x)^2', 'tan(x)^3/3+tan(x)^5/5',
  { domain: D.trig,
  hints: ['$\\sec^{2}x$ 하나를 $dx$ 쪽에 남기고 나머지를 $\\tan$ 으로 바꾼다.',
          '$\\sec^{2}x=1+\\tan^{2}x$'],
  steps: ['$u=\\tan x,\\ du=\\sec^{2}x\\,dx$',
          '$\\int(1+u^{2})u^{2}du=\\dfrac{u^{3}}{3}+\\dfrac{u^{5}}{5}$'] });

add('hard', '항등식 정리', 'sqrt(csc(x)-sin(x))', '2*sqrt(sin(x))',
  { domain: [0.25, 1.4],
  hints: ['$\\csc x-\\sin x=\\dfrac{1-\\sin^{2}x}{\\sin x}=\\dfrac{\\cos^{2}x}{\\sin x}$',
          '근호를 벗기면 $\\dfrac{\\cos x}{\\sqrt{\\sin x}}$ 다.'],
  steps: ['$\\csc x-\\sin x=\\dfrac{\\cos^{2}x}{\\sin x}$',
          '$\\int\\dfrac{\\cos x}{\\sqrt{\\sin x}}dx$ 는 $u=\\sin x$ 로 끝',
          '$=2\\sqrt{\\sin x}$'] });

add('hard', '차수 낮추기', 'cos(x)^6',
    '5*x/16+15*sin(2*x)/64+3*sin(4*x)/64+sin(6*x)/192',
  { domain: D.trigW,
  hints: ['$\\cos^{2}x=\\dfrac{1+\\cos2x}{2}$ 를 세 번 쓴다.',
          '$\\cos^{6}x=\\dfrac{10+15\\cos2x+6\\cos4x+\\cos6x}{32}$'],
  steps: ['배각 공식으로 차수를 낮춘다',
          '$\\cos^{6}x=\\dfrac{10+15\\cos2x+6\\cos4x+\\cos6x}{32}$',
          '항마다 적분한다'] });

add('medium', '삼각 치환', '1/(x^4+2*x^2+1)', 'x/(2*(x^2+1))+atan(x)/2',
  { domain: D.all,
  hints: ['$x^{4}+2x^{2}+1=(x^{2}+1)^{2}$ 이다.',
          '$x=\\tan\\theta$ 로 두면 $\\int\\cos^{2}\\theta\\,d\\theta$ 다.'],
  steps: ['$(x^{2}+1)^{2}$ 로 묶는다',
          '$x=\\tan\\theta$ 치환 후 차수를 낮춘다',
          '$=\\dfrac{x}{2(x^{2}+1)}+\\dfrac{\\arctan x}{2}$'] });

add('hard', '순환 부분적분', 'cos(ln(x))', 'x*(cos(ln(x))+sin(ln(x)))/2',
  { domain: D.pos,
  hints: ['부분적분을 두 번 하면 원래 적분이 다시 나온다.',
          '$t=\\ln x$ 로 두고 $\\int e^{t}\\cos t\\,dt$ 로 봐도 된다.'],
  steps: ['$t=\\ln x\\Rightarrow\\int e^{t}\\cos t\\,dt$',
          '$=\\dfrac{e^{t}(\\cos t+\\sin t)}{2}$',
          '$=\\dfrac{x(\\cos(\\ln x)+\\sin(\\ln x))}{2}$'] });

add('hard', '유리화', '1/(9*cos(x)^2+4*sin(x)^2)', 'atan(2*tan(x)/3)/6',
  { domain: D.trig,
  hints: ['분자·분모를 $\\cos^{2}x$ 로 나눈다.',
          '$\\dfrac{\\sec^{2}x}{9+4\\tan^{2}x}$ 에서 $u=\\tan x$'],
  steps: ['$\\dfrac{\\sec^{2}x\\,dx}{9+4\\tan^{2}x}$',
          '$u=\\tan x\\Rightarrow\\int\\dfrac{du}{9+4u^{2}}$',
          '$=\\dfrac{1}{6}\\arctan\\dfrac{2\\tan x}{3}$'] });

add('monster', '역수 치환', '1/(x^2*(x^4+1)^(3/4))', '-(x^4+1)^(1/4)/x',
  { domain: [0.4, 2.6],
  hints: ['$(x^{4}+1)^{3/4}=x^{3}\\left(1+x^{-4}\\right)^{3/4}$ 로 $x$ 를 뽑아낸다.',
          '$u=1+x^{-4}$ 로 두면 $du=-4x^{-5}dx$ 다.'],
  steps: ['피적분함수를 $x^{-5}(1+x^{-4})^{-3/4}$ 로 고친다',
          '$u=1+x^{-4}\\Rightarrow-\\dfrac14\\int u^{-3/4}du=-u^{1/4}$',
          '$=-\\dfrac{(x^{4}+1)^{1/4}}{x}$'] });

addDef('hard', '곱-합 공식', 'cos(x)*cos(3*x)*cos(5*x)', '0',
  { lo: '0', hi: 'pi',
  hints: ['곱을 합으로 바꾸면 $\\cos kx$ 들만 남는다.',
          '$\\int_{0}^{\\pi}\\cos kx\\,dx=0$ (정수 $k\\neq0$)'],
  steps: ['$\\cos x\\cos3x\\cos5x=\\dfrac{\\cos9x+\\cos7x+\\cos3x+\\cos x}{4}$',
          '$k=1,3,7,9$ 모두 $\\int_{0}^{\\pi}\\cos kx\\,dx=0$',
          '$=0$'] });

add('hard', '미분 되짚기', '1/ln(x)+ln(ln(x))', 'x*ln(ln(x))',
  { domain: D.lnln,
  hints: ['$\\left(x\\ln(\\ln x)\\right)\'$ 를 계산해 보라.',
          '곱의 미분법으로 $\\ln(\\ln x)+\\dfrac{1}{\\ln x}$ 가 나온다.'],
  steps: ['$\\left(x\\ln(\\ln x)\\right)\'=\\ln(\\ln x)+x\\cdot\\dfrac{1}{x\\ln x}$',
          '$=\\ln(\\ln x)+\\dfrac{1}{\\ln x}$',
          '$=x\\ln(\\ln x)$'] });

add('medium', '지수 유리식', '1/(2+e^x)', 'x/2-ln(2+e^x)/2',
  { domain: D.all,
  hints: ['$\\dfrac{1}{2+e^{x}}=\\dfrac12\\left(1-\\dfrac{e^{x}}{2+e^{x}}\\right)$',
          '뒤쪽은 분모의 도함수가 분자다.'],
  steps: ['둘로 쪼갠다', '$=\\dfrac{x}{2}-\\dfrac{\\ln(2+e^{x})}{2}$'] });

add('monster', '이항 미분식', 'sqrt(x/(1-x^3))', '(2/3)*asin(x^(3/2))',
  { domain: [0.1, 0.85],
  hints: ['$u=x^{3/2}$ 로 두면 $du=\\dfrac32\\sqrt x\\,dx$ 다.',
          '$1-x^{3}=1-u^{2}$ 가 된다.'],
  steps: ['$u=x^{3/2}\\Rightarrow\\dfrac23\\displaystyle\\int\\dfrac{du}{\\sqrt{1-u^{2}}}$',
          '$=\\dfrac23\\arcsin u=\\dfrac23\\arcsin\\left(x^{3/2}\\right)$'] });

add('medium', '치환적분', '4*x/(1-x^4)', 'ln((1+x^2)/(1-x^2))',
  { domain: [0.15, 0.85], lnAbs: true,
  hints: ['$u=x^{2}$ 로 두면 $2\\int\\dfrac{du}{1-u^{2}}$ 다.',
          '$\\int\\dfrac{du}{1-u^{2}}=\\dfrac12\\ln\\left|\\dfrac{1+u}{1-u}\\right|$'],
  steps: ['$u=x^{2}$ 치환', '$=\\ln\\left|\\dfrac{1+x^{2}}{1-x^{2}}\\right|$'] });

addDef('medium', '넓이로 읽기', 'sqrt(6*x-x^2)', '9*pi/2',
  { lo: '0', hi: '6',
  hints: ['완전제곱: $6x-x^{2}=9-(x-3)^{2}$',
          '반지름 $3$ 인 반원의 넓이다.'],
  steps: ['$\\sqrt{9-(x-3)^{2}}$ 는 중심 $(3,0)$, 반지름 $3$ 인 위쪽 반원',
          '$=\\dfrac{\\pi\\cdot3^{2}}{2}=\\dfrac{9\\pi}{2}$'] });

add('monster', '미분 되짚기', 'sin(101*x)*sin(x)^99', 'sin(x)^100*sin(100*x)/100',
  { domain: [1.2, 1.9],
  hints: ['$\\sin^{100}x\\,\\sin(100x)$ 를 미분해 보라.',
          '$\\cos x\\sin100x+\\sin x\\cos100x=\\sin(101x)$ 로 합쳐진다.'],
  steps: ['$\\left(\\dfrac{\\sin^{100}x\\sin100x}{100}\\right)\'=\\sin^{99}x\\cos x\\sin100x+\\sin^{100}x\\cos100x$',
          '$=\\sin^{99}x\\left(\\cos x\\sin100x+\\sin x\\cos100x\\right)$',
          '$=\\sin^{99}x\\sin(101x)$'] });

add('hard', '이중 지수', 'x*e^(e^(x^2)+x^2)', 'e^(e^(x^2))/2',
  { domain: [0.2, 1.3],
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\int e^{e^{u}}e^{u}du$ 다.',
          '다시 $v=e^{u}$ 로 두면 $\\dfrac12\\int e^{v}dv$ 다.'],
  steps: ['$u=x^{2}$, 그다음 $v=e^{u}$',
          '$=\\dfrac{e^{v}}{2}=\\dfrac{e^{e^{x^{2}}}}{2}$'] });

addDef('hard', '평행이동', '(x^3-3*x^2+3*x-1)/(x^4+4*x^3+6*x^2+4*x+1)', 'ln(2)-5/6',
  { lo: '0', hi: '1',
  hints: ['분자는 $(x-1)^{3}$, 분모는 $(x+1)^{4}$ 다.',
          '$t=x+1$ 로 옮기면 $\\dfrac{(t-2)^{3}}{t^{4}}$ 가 된다.'],
  steps: ['$t=x+1\\Rightarrow\\displaystyle\\int_{1}^{2}\\dfrac{t^{3}-6t^{2}+12t-8}{t^{4}}dt$',
          '$\\left[\\ln t+\\dfrac6t-\\dfrac{6}{t^{2}}+\\dfrac{8}{3t^{3}}\\right]_{1}^{2}$',
          '$=\\ln2-\\dfrac56$'] });

add('hard', '유리화', 'sqrt((1-x)/(1+x))', 'asin(x)+sqrt(1-x^2)',
  { domain: D.unit,
  hints: ['분자·분모에 $\\sqrt{1-x}$ 를 곱해 $\\dfrac{1-x}{\\sqrt{1-x^{2}}}$ 로 만든다.',
          '두 조각으로 나누면 각각 표준형이다.'],
  steps: ['$\\dfrac{1-x}{\\sqrt{1-x^{2}}}=\\dfrac{1}{\\sqrt{1-x^{2}}}-\\dfrac{x}{\\sqrt{1-x^{2}}}$',
          '$=\\arcsin x+\\sqrt{1-x^{2}}$'] });


// --- 2012 -----------------------------------------------------------

add('medium', '거듭제곱근 치환', '1/(sqrt(x)-1)', '2*sqrt(x)+2*ln(sqrt(x)-1)',
  { domain: [1.4, 4.0], lnAbs: true,
  hints: ['$u=\\sqrt x$ 로 두면 $dx=2u\\,du$ 다.',
          '$\\dfrac{2u}{u-1}=2+\\dfrac{2}{u-1}$'],
  steps: ['$u=\\sqrt x$ 치환', '$\\int\\left(2+\\dfrac{2}{u-1}\\right)du=2u+2\\ln|u-1|$',
          '$=2\\sqrt x+2\\ln\\left|\\sqrt x-1\\right|$'] });

add('medium', '부분적분', 'x^(1/4)*ln(x)', '(4/5)*x^(5/4)*ln(x)-(16/25)*x^(5/4)',
  { domain: D.pos,
  hints: ['$u=\\ln x,\\ dv=x^{1/4}dx$ 로 둔다.',
          '$v=\\dfrac45x^{5/4}$'],
  steps: ['부분적분 $\\Rightarrow\\dfrac45x^{5/4}\\ln x-\\dfrac45\\displaystyle\\int x^{1/4}dx$',
          '$=\\dfrac45x^{5/4}\\ln x-\\dfrac{16}{25}x^{5/4}$'] });

add('monster', '이중 치환', '1/((1+sqrt(x))*sqrt(x-x^2))',
    '-2*sqrt((1-sqrt(x))/(1+sqrt(x)))',
  { domain: [0.1, 0.85],
  hints: ['$\\sqrt{x-x^{2}}=\\sqrt x\\sqrt{1-x}$ 이므로 $u=\\sqrt x$ 로 두면 $\\dfrac{2\\,du}{(1+u)\\sqrt{1-u^{2}}}$ 다.',
          '다시 $w=\\sqrt{\\dfrac{1-u}{1+u}}$ 로 두면 피적분함수가 상수가 된다.'],
  steps: ['$u=\\sqrt x\\Rightarrow2\\displaystyle\\int\\dfrac{du}{(1+u)^{3/2}(1-u)^{1/2}}$',
          '$w=\\sqrt{\\dfrac{1-u}{1+u}}$ 로 두면 적분이 $-2\\int dw$ 로 바뀐다',
          '$=-2\\sqrt{\\dfrac{1-\\sqrt x}{1+\\sqrt x}}$'] });

add('hard', '거듭제곱근 치환', '1/(sqrt(x)*(x^(1/4)+1)^10)',
    '-1/(2*(x^(1/4)+1)^8)+4/(9*(x^(1/4)+1)^9)',
  { domain: D.pos,
  hints: ['$u=x^{1/4}$ 로 두면 $dx=4u^{3}du$ 다.',
          '$\\dfrac{4u}{(u+1)^{10}}$ 에서 $u=(u+1)-1$ 로 쪼갠다.'],
  steps: ['$u=x^{1/4}\\Rightarrow4\\displaystyle\\int\\dfrac{u\\,du}{(u+1)^{10}}$',
          '$=4\\int\\left((u+1)^{-9}-(u+1)^{-10}\\right)du$',
          '$=-\\dfrac{1}{2(u+1)^{8}}+\\dfrac{4}{9(u+1)^{9}}$'] });

addDef('medium', '항등식 정리', 'sin(acos(x))', 'pi/4',
  { lo: '0', hi: '1',
  hints: ['$\\sin(\\arccos x)=\\sqrt{1-x^{2}}$ 다.',
          '사분원의 넓이로 읽으면 끝이다.'],
  steps: ['$\\sin(\\arccos x)=\\sqrt{1-x^{2}}$',
          '$\\int_{0}^{1}\\sqrt{1-x^{2}}dx$ 는 반지름 $1$ 인 사분원의 넓이',
          '$=\\dfrac{\\pi}{4}$'] });

add('medium', '완전제곱', '1/sqrt(1-4*x-x^2)', 'asin((x+2)/sqrt(5))',
  { domain: [-1.5, 0.15],
  hints: ['$1-4x-x^{2}=5-(x+2)^{2}$ 로 완전제곱한다.',
          '$\\int\\dfrac{dx}{\\sqrt{a^{2}-u^{2}}}=\\arcsin\\dfrac{u}{a}$'],
  steps: ['$5-(x+2)^{2}$ 로 정리',
          '$=\\arcsin\\dfrac{x+2}{\\sqrt5}$'] });

addDef('medium', '삼각 유리식', '1/(1+sin(x))', '1',
  { lo: '0', hi: 'pi/2',
  hints: ['분자·분모에 $1-\\sin x$ 를 곱해 보라.',
          '$\\int\\dfrac{dx}{1+\\sin x}=\\tan x-\\sec x$'],
  steps: ['$\\dfrac{1-\\sin x}{\\cos^{2}x}=\\sec^{2}x-\\sec x\\tan x$',
          '$\\left[\\tan x-\\sec x\\right]_{0}^{\\pi/2}$, 위끝은 극한으로 $0$',
          '$=0-(-1)=1$'] });

addDef('hard', '킹 성질', 'sqrt(x)/(sqrt(2012-x)+sqrt(x))', '1005',
  { lo: '1', hi: '2011',
  hints: ['$a+b=2012$ 이므로 $x\\to2012-x$ 를 넣어 보라.',
          '원래 식과 더하면 분자가 분모와 같아진다.'],
  steps: ['$f(x)+f(2012-x)=1$',
          '$2I=2011-1=2010$',
          '$I=1005$'] });

add('monster', '역수 치환', '(x-1)/((x+1)*sqrt(x^3+x^2+x))', '2*acos(sqrt(x)/(x+1))',
  { domain: [0.4, 2.4],
  hints: ['$x^{3}+x^{2}+x=x\\left(x+1+\\dfrac1x\\right)\\cdot x$ 로 보고 $\\sqrt x$ 를 뽑아낸다.',
          '$w=\\sqrt x+\\dfrac{1}{\\sqrt x}$ 로 두면 $dw=\\dfrac{x-1}{2x^{3/2}}dx$ 다.'],
  steps: ['$\\sqrt{x^{3}+x^{2}+x}=x\\sqrt{w^{2}-1}$ (여기서 $w=\\sqrt x+1/\\sqrt x$)',
          '$x+1=\\sqrt x\\,w$ 를 쓰면 적분이 $2\\displaystyle\\int\\dfrac{dw}{w\\sqrt{w^{2}-1}}$',
          '$=2\\operatorname{arcsec}w=2\\arccos\\dfrac{\\sqrt x}{x+1}$'] });

addDef('hard', '평행이동', '(x^4+4*x^3+6*x^2+4*x+1)/(x^3-3*x^2+3*x-1)', '33/2-24*ln(2)',
  { lo: '-1', hi: '0',
  hints: ['분자는 $(x+1)^{4}$, 분모는 $(x-1)^{3}$ 이다.',
          '$t=x-1$ 로 옮기면 $\\dfrac{(t+2)^{4}}{t^{3}}$ 이 된다.'],
  steps: ['$t=x-1\\Rightarrow\\displaystyle\\int_{-2}^{-1}\\left(t+8+\\dfrac{24}{t}+\\dfrac{32}{t^{2}}+\\dfrac{16}{t^{3}}\\right)dt$',
          '$\\left[\\dfrac{t^{2}}{2}+8t+24\\ln|t|-\\dfrac{32}{t}-\\dfrac{8}{t^{2}}\\right]_{-2}^{-1}$',
          '$=\\dfrac{33}{2}-24\\ln2$'] });

add('medium', '곱의 미분 되짚기', 'cos(x)*ln(x)+sin(x)/x', 'sin(x)*ln(x)',
  { domain: D.pos,
  hints: ['$(\\sin x\\ln x)\'$ 를 계산해 보라.',
          '곱의 미분법 그대로다.'],
  steps: ['$(\\sin x\\ln x)\'=\\cos x\\ln x+\\dfrac{\\sin x}{x}$', '$=\\sin x\\ln x$'] });

add('medium', '부분분수', '1/(x^3-x)', '-ln(x)+ln(x-1)/2+ln(x+1)/2',
  { domain: [1.4, 3.4], lnAbs: true,
  hints: ['$x^{3}-x=x(x-1)(x+1)$ 이다.',
          '$\\dfrac{1}{x(x-1)(x+1)}=-\\dfrac1x+\\dfrac{1}{2(x-1)}+\\dfrac{1}{2(x+1)}$'],
  steps: ['부분분수로 쪼갠다', '항마다 로그로 적분한다'] });

addDef('hard', '부분적분', 'x*asin(x)/sqrt(1-x^2)', '1/2-pi*sqrt(3)/12',
  { lo: '0', hi: '1/2',
  hints: ['$u=\\arcsin x,\\ dv=\\dfrac{x\\,dx}{\\sqrt{1-x^{2}}}$ 로 둔다.',
          '$v=-\\sqrt{1-x^{2}}$ 이고 $u\'v$ 가 $-1$ 로 딱 떨어진다.'],
  steps: ['부분적분 $\\Rightarrow-\\sqrt{1-x^{2}}\\arcsin x+x$',
          '$x=\\dfrac12$ 에서 $-\\dfrac{\\sqrt3}{2}\\cdot\\dfrac{\\pi}{6}+\\dfrac12$',
          '$=\\dfrac12-\\dfrac{\\pi\\sqrt3}{12}$'] });

addDef('hard', '베타 함수', 'x*(1-x)^99', '1/10100',
  { lo: '0', hi: '1',
  hints: ['$B(m,n)=\\displaystyle\\int_{0}^{1}x^{m-1}(1-x)^{n-1}dx=\\dfrac{(m-1)!(n-1)!}{(m+n-1)!}$',
          '여기서는 $m=2,\\ n=100$ 이다.'],
  steps: ['$B(2,100)=\\dfrac{1!\\cdot99!}{101!}$',
          '$=\\dfrac{1}{100\\cdot101}=\\dfrac{1}{10100}$'] });

addDef('hard', '배각 공식', 'sin(4*x)/sin(x)', '4/3',
  { lo: '0', hi: 'pi/2',
  hints: ['$\\sin4x=2\\sin2x\\cos2x=4\\sin x\\cos x\\cos2x$',
          '약분하면 $4\\cos x\\cos2x$ 만 남는다.'],
  steps: ['$\\dfrac{\\sin4x}{\\sin x}=4\\cos x\\cos2x=2(\\cos3x+\\cos x)$',
          '$2\\left[\\dfrac{\\sin3x}{3}+\\sin x\\right]_{0}^{\\pi/2}$',
          '$=2\\left(-\\dfrac13+1\\right)=\\dfrac43$'] });

add('hard', '거듭제곱근 치환', 'x^(-1/2)/(1+x^(1/3))', '6*x^(1/6)-6*atan(x^(1/6))',
  { domain: D.pos,
  hints: ['분모 지수 $2$ 와 $3$ 의 최소공배수를 보고 $x=u^{6}$ 으로 둔다.',
          '$6\\displaystyle\\int\\dfrac{u^{2}}{1+u^{2}}du$ 가 된다.'],
  steps: ['$x=u^{6}$ 치환',
          '$6\\int\\left(1-\\dfrac{1}{1+u^{2}}\\right)du=6u-6\\arctan u$',
          '$=6x^{1/6}-6\\arctan\\left(x^{1/6}\\right)$'] });

add('medium', '표준형 정리', '1/sqrt(2*x^2-1)', 'ln(x+sqrt(x^2-1/2))/sqrt(2)',
  { domain: [0.9, 3.0], lnAbs: true,
  hints: ['$\\sqrt2$ 를 밖으로 빼면 $\\dfrac{1}{\\sqrt2}\\displaystyle\\int\\dfrac{dx}{\\sqrt{x^{2}-1/2}}$ 다.',
          '$\\int\\dfrac{dx}{\\sqrt{x^{2}-a^{2}}}=\\ln\\left|x+\\sqrt{x^{2}-a^{2}}\\right|$'],
  steps: ['$\\dfrac{1}{\\sqrt2}\\int\\dfrac{dx}{\\sqrt{x^{2}-\\frac12}}$',
          '$=\\dfrac{1}{\\sqrt2}\\ln\\left|x+\\sqrt{x^{2}-\\tfrac12}\\right|$'] });

add('hard', '지수 치환', '1/sqrt(e^x-1)', '2*atan(sqrt(e^x-1))',
  { domain: [0.15, 2.2],
  hints: ['$u=\\sqrt{e^{x}-1}$ 로 두면 $e^{x}=u^{2}+1$ 이다.',
          '$dx=\\dfrac{2u\\,du}{u^{2}+1}$'],
  steps: ['$u=\\sqrt{e^{x}-1}$ 치환',
          '$\\int\\dfrac1u\\cdot\\dfrac{2u}{u^{2}+1}du=2\\arctan u$',
          '$=2\\arctan\\sqrt{e^{x}-1}$'] });

add('medium', '치환적분', 'x/(x^4+4)', 'atan(x^2/2)/4',
  { domain: D.poly,
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\displaystyle\\int\\dfrac{du}{u^{2}+4}$ 다.',
          '$\\int\\dfrac{du}{u^{2}+a^{2}}=\\dfrac1a\\arctan\\dfrac ua$'],
  steps: ['$u=x^{2}$ 치환', '$=\\dfrac14\\arctan\\dfrac{x^{2}}{2}$'] });

add('hard', '위상 이동', '2/(cos(x)-sin(x))^2', 'tan(x+pi/4)',
  { domain: [0.9, 2.2],
  hints: ['$\\cos x-\\sin x=\\sqrt2\\cos\\left(x+\\dfrac\\pi4\\right)$',
          '제곱하면 $2\\cos^{2}\\left(x+\\dfrac\\pi4\\right)$ 다.'],
  steps: ['$\\dfrac{2}{2\\cos^{2}(x+\\pi/4)}=\\sec^{2}\\left(x+\\dfrac\\pi4\\right)$',
          '$=\\tan\\left(x+\\dfrac\\pi4\\right)$'] });

add('hard', '부분적분', 'x*cosh(x)/sinh(x)^2', '-x/sinh(x)+ln(tanh(x/2))',
  { domain: [0.3, 1.6], lnAbs: true,
  hints: ['$\\dfrac{\\cosh x}{\\sinh^{2}x}dx=d\\left(-\\dfrac{1}{\\sinh x}\\right)$ 다.',
          '$\\int\\operatorname{csch}x\\,dx=\\ln\\left|\\tanh\\dfrac x2\\right|$'],
  steps: ['부분적분 $\\Rightarrow-\\dfrac{x}{\\sinh x}+\\displaystyle\\int\\dfrac{dx}{\\sinh x}$',
          '$=-\\dfrac{x}{\\sinh x}+\\ln\\left|\\tanh\\dfrac x2\\right|$'] });

addDef('medium', '치환적분', 'x^5*sqrt(1+x^3)', '1192/45',
  { lo: '0', hi: '2',
  hints: ['$t=1+x^{3}$ 으로 두면 $x^{3}=t-1$ 이다.',
          '$x^{5}dx=x^{3}\\cdot x^{2}dx=\\dfrac{(t-1)dt}{3}$'],
  steps: ['$t=1+x^{3}\\Rightarrow\\dfrac13\\displaystyle\\int_{1}^{9}\\left(t^{3/2}-t^{1/2}\\right)dt$',
          '$=\\dfrac13\\left[\\dfrac{2t^{5/2}}{5}-\\dfrac{2t^{3/2}}{3}\\right]_{1}^{9}=\\dfrac{1192}{45}$'] });

addDef('monster', '프룰라니 적분', '(x^7-1)/ln(x)', 'ln(8)',
  { lo: '0', hi: '1',
  hints: ['$I(a)=\\displaystyle\\int_{0}^{1}\\dfrac{x^{a}-1}{\\ln x}dx$ 로 두고 $a$ 로 미분한다.',
          '$I\'(a)=\\displaystyle\\int_{0}^{1}x^{a}dx=\\dfrac{1}{a+1}$'],
  steps: ['$I\'(a)=\\dfrac{1}{a+1}$, $I(0)=0$',
          '$I(a)=\\ln(a+1)$',
          '$a=7\\Rightarrow\\ln8$'] });


// --- 2013 -----------------------------------------------------------

add('medium', '로그 법칙', 'ln(x^2)-2*ln(2*x)', '-2*x*ln(2)',
  { domain: D.pos,
  hints: ['$\\ln(x^{2})=2\\ln x$, $\\ln(2x)=\\ln2+\\ln x$ 다.',
          '$x$ 항이 모두 상쇄되어 상수만 남는다.'],
  steps: ['$2\\ln x-2(\\ln2+\\ln x)=-2\\ln2$',
          '상수의 적분이므로 $=-2x\\ln2$'] });

addDef('medium', '절댓값 나누기', 'e^(|x|)', 'e+e^3-2',
  { lo: '-1', hi: '3',
  hints: ['$x<0$ 과 $x>0$ 으로 구간을 나눈다.',
          '$\\int_{-1}^{0}e^{-x}dx+\\int_{0}^{3}e^{x}dx$'],
  steps: ['$\\int_{-1}^{0}e^{-x}dx=e-1$',
          '$\\int_{0}^{3}e^{x}dx=e^{3}-1$',
          '$=e+e^{3}-2$'] });

add('hard', '몫의 미분 되짚기', '(ln(x)*cos(x)-sin(x)/x)/ln(x)^2', 'sin(x)/ln(x)',
  { domain: D.lnln,
  hints: ['답이 $\\dfrac{f}{\\ln x}$ 꼴이라고 짐작하고 몫의 미분법을 써 보라.',
          '$\\left(\\dfrac{\\sin x}{\\ln x}\\right)\'$ 를 계산해 보라.'],
  steps: ['$\\left(\\dfrac{\\sin x}{\\ln x}\\right)\'=\\dfrac{\\cos x\\ln x-\\sin x\\cdot\\frac1x}{\\ln^{2}x}$',
          '피적분함수와 같으므로 $=\\dfrac{\\sin x}{\\ln x}$'] });

addDef('easy', '완전세제곱', 'x^3-3*x^2+3*x-1', '2500',
  { lo: '1', hi: '11',
  hints: ['$x^{3}-3x^{2}+3x-1=(x-1)^{3}$ 이다.',
          '$\\int(x-1)^{3}dx=\\dfrac{(x-1)^{4}}{4}$'],
  steps: ['$(x-1)^{3}$ 으로 묶는다',
          '$\\left[\\dfrac{(x-1)^{4}}{4}\\right]_{1}^{11}=\\dfrac{10^{4}}{4}=2500$'] });

addDef('medium', '넓이로 읽기', 'sqrt(12-3*x^2)', 'sqrt(3)*pi',
  { lo: '0', hi: '2',
  hints: ['$\\sqrt{12-3x^{2}}=\\sqrt3\\sqrt{4-x^{2}}$ 로 묶는다.',
          '$\\int_{0}^{2}\\sqrt{4-x^{2}}dx$ 는 반지름 $2$ 인 사분원의 넓이다.'],
  steps: ['$\\sqrt3\\displaystyle\\int_{0}^{2}\\sqrt{4-x^{2}}dx$',
          '$=\\sqrt3\\cdot\\dfrac{\\pi\\cdot2^{2}}{4}=\\sqrt3\\,\\pi$'] });

addDef('hard', '대칭 논법', 'x+(x-3)^7+sin(x-3)', '18',
  { lo: '0', hi: '6',
  hints: ['구간의 한가운데가 $x=3$ 이다.',
          '$(x-3)^{7}$ 과 $\\sin(x-3)$ 은 $x=3$ 에 대해 홀함수다.'],
  steps: ['홀함수 두 항은 대칭 구간에서 $0$',
          '$\\int_{0}^{6}x\\,dx=18$'] });

add('medium', '항등식 정리', 'sin(x)*sqrt(1+tan(x)^2)', '-ln(cos(x))',
  { domain: D.trig, lnAbs: true,
  hints: ['$1+\\tan^{2}x=\\sec^{2}x$ 다.',
          '근호를 벗기면 $\\sin x\\sec x=\\tan x$ 다.'],
  steps: ['$\\sqrt{1+\\tan^{2}x}=|\\sec x|$',
          '$\\sin x\\sec x=\\tan x$',
          '$\\int\\tan x\\,dx=-\\ln|\\cos x|$'] });

add('hard', '인수분해', '(x^5-x^3+x^2-1)/(x^4-x^3+x-1)', 'x^2/2+x',
  { domain: [1.4, 3.4],
  hints: ['분모는 $x^{3}(x-1)+(x-1)$ 로 묶인다.',
          '분자는 $x^{3}(x^{2}-1)+(x^{2}-1)$ 로 묶인다.'],
  steps: ['분모 $=(x-1)(x+1)(x^{2}-x+1)$',
          '분자 $=(x^{2}-1)(x^{3}+1)=(x-1)(x+1)^{2}(x^{2}-x+1)$',
          '약분하면 $x+1$ 만 남는다'] });

addDef('medium', '이상적분', 'ln(x)', '-1',
  { lo: '0', hi: '1',
  hints: ['$\\int\\ln x\\,dx=x\\ln x-x$ 다.',
          '$x\\to0^{+}$ 에서 $x\\ln x\\to0$ 이다.'],
  steps: ['$\\left[x\\ln x-x\\right]_{0}^{1}$',
          '위끝 $=-1$, 아래끝 $=0$',
          '$=-1$'] });

add('medium', '지수 유리식', '1/(1-e^(-x))', 'ln(e^x-1)',
  { domain: [0.25, 2.2], lnAbs: true,
  hints: ['분자·분모에 $e^{x}$ 를 곱해 $\\dfrac{e^{x}}{e^{x}-1}$ 로 만든다.',
          '분모의 도함수가 분자다.'],
  steps: ['$\\dfrac{e^{x}}{e^{x}-1}$ 로 고친다', '$=\\ln\\left|e^{x}-1\\right|$'] });

addDef('medium', '차수 낮추기', 'sin(x)^2*cos(x)^2', 'pi/8',
  { lo: '0', hi: 'pi',
  hints: ['$\\sin x\\cos x=\\dfrac{\\sin2x}{2}$ 다.',
          '$\\sin^{2}2x$ 의 평균은 $\\dfrac12$ 다.'],
  steps: ['$\\dfrac{\\sin^{2}2x}{4}$ 로 고친다',
          '$\\dfrac14\\int_{0}^{\\pi}\\sin^{2}2x\\,dx=\\dfrac14\\cdot\\dfrac{\\pi}{2}$',
          '$=\\dfrac{\\pi}{8}$'] });

addDef('hard', '치환적분', 'pi*sin(pi*sqrt(x))/sqrt(x)', '4',
  { lo: '0', hi: '441',
  hints: ['$u=\\sqrt x$ 로 두면 $\\dfrac{dx}{\\sqrt x}=2\\,du$ 다.',
          '$441=21^{2}$ 이므로 $u$ 는 $0$ 에서 $21$ 까지다.'],
  steps: ['$u=\\sqrt x\\Rightarrow2\\pi\\displaystyle\\int_{0}^{21}\\sin(\\pi u)du$',
          '$=2\\left[-\\cos(\\pi u)\\right]_{0}^{21}=2(1+1)$',
          '$=4$'] });

add('hard', '거듭제곱근 치환', 'e^(x^(1/4))',
    '4*e^(x^(1/4))*(x^(3/4)-3*sqrt(x)+6*x^(1/4)-6)',
  { domain: D.pos,
  hints: ['$u=x^{1/4}$ 로 두면 $dx=4u^{3}du$ 다.',
          '$\\int u^{3}e^{u}du$ 는 부분적분 세 번이다.'],
  steps: ['$u=x^{1/4}\\Rightarrow4\\displaystyle\\int u^{3}e^{u}du$',
          '$\\int u^{3}e^{u}du=e^{u}(u^{3}-3u^{2}+6u-6)$',
          '$u$ 를 되돌린다'] });

add('hard', '항등식 정리', 'cos(x)*cot(x)', 'ln(tan(x/2))+cos(x)',
  { domain: [0.3, 1.5], lnAbs: true,
  hints: ['$\\cos x\\cot x=\\dfrac{\\cos^{2}x}{\\sin x}=\\dfrac{1-\\sin^{2}x}{\\sin x}$',
          '$=\\csc x-\\sin x$ 로 갈라진다.'],
  steps: ['$\\csc x-\\sin x$ 로 쪼갠다',
          '$\\int\\csc x\\,dx=\\ln\\left|\\tan\\dfrac x2\\right|$',
          '$=\\ln\\left|\\tan\\dfrac x2\\right|+\\cos x$'] });

add('medium', '다항식 나눗셈', 'x^3/(1+x^2)', 'x^2/2-ln(1+x^2)/2',
  { domain: D.all,
  hints: ['$\\dfrac{x^{3}}{1+x^{2}}=x-\\dfrac{x}{1+x^{2}}$ 다.',
          '뒤쪽은 $u=1+x^{2}$ 치환이다.'],
  steps: ['나눗셈으로 쪼갠다', '$=\\dfrac{x^{2}}{2}-\\dfrac{\\ln(1+x^{2})}{2}$'] });

add('medium', '완전제곱', '1/(2-2*x+x^2)', 'atan(x-1)',
  { domain: D.all,
  hints: ['$x^{2}-2x+2=(x-1)^{2}+1$ 이다.',
          '$\\int\\dfrac{du}{u^{2}+1}=\\arctan u$'],
  steps: ['완전제곱 후 $u=x-1$', '$=\\arctan(x-1)$'] });

add('hard', '부분적분', 'sin(x)*ln(sin(x))',
    '-cos(x)*ln(sin(x))+ln(tan(x/2))+cos(x)',
  { domain: [0.3, 1.5], lnAbs: true,
  hints: ['$u=\\ln(\\sin x),\\ dv=\\sin x\\,dx$ 로 둔다.',
          '남는 적분이 $\\displaystyle\\int\\dfrac{\\cos^{2}x}{\\sin x}dx=\\int(\\csc x-\\sin x)dx$ 다.'],
  steps: ['부분적분 $\\Rightarrow-\\cos x\\ln(\\sin x)+\\displaystyle\\int\\dfrac{\\cos^{2}x}{\\sin x}dx$',
          '$\\int(\\csc x-\\sin x)dx=\\ln\\left|\\tan\\dfrac x2\\right|+\\cos x$'] });

add('medium', '치환적분', 'x/(1-x^4)', 'ln((1+x^2)/(1-x^2))/4',
  { domain: [0.15, 0.85], lnAbs: true,
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\displaystyle\\int\\dfrac{du}{1-u^{2}}$ 다.',
          '$\\int\\dfrac{du}{1-u^{2}}=\\dfrac12\\ln\\left|\\dfrac{1+u}{1-u}\\right|$'],
  steps: ['$u=x^{2}$ 치환', '$=\\dfrac14\\ln\\left|\\dfrac{1+x^{2}}{1-x^{2}}\\right|$'] });

add('hard', '삼각 치환', 'sqrt(12-3*x^2)', 'sqrt(3)*(x*sqrt(4-x^2)/2+2*asin(x/2))',
  { domain: [-1.5, 1.7],
  hints: ['$\\sqrt3$ 를 밖으로 빼고 $x=2\\sin\\theta$ 로 둔다.',
          '$\\int\\sqrt{a^{2}-x^{2}}dx=\\dfrac{x\\sqrt{a^{2}-x^{2}}}{2}+\\dfrac{a^{2}}{2}\\arcsin\\dfrac xa$'],
  steps: ['$\\sqrt3\\displaystyle\\int\\sqrt{4-x^{2}}dx$',
          '$=\\sqrt3\\left(\\dfrac{x\\sqrt{4-x^{2}}}{2}+2\\arcsin\\dfrac x2\\right)$'] });

add('hard', '삼각 치환', 'sec(x)^5*tan(x)^3', '(1/cos(x))^7/7-(1/cos(x))^5/5',
  { domain: D.trig,
  hints: ['$\\sec x\\tan x\\,dx$ 를 $du$ 로 남기고 나머지를 $\\sec$ 로 바꾼다.',
          '$\\tan^{2}x=\\sec^{2}x-1$'],
  steps: ['$u=\\sec x$ 치환',
          '$\\int u^{4}(u^{2}-1)du=\\dfrac{u^{7}}{7}-\\dfrac{u^{5}}{5}$'] });

addDef('hard', '삼각 유리식', '1/(1-sin(x))', '2',
  { lo: '-pi/4', hi: 'pi/4',
  hints: ['분자·분모에 $1+\\sin x$ 를 곱한다.',
          '$\\int\\dfrac{dx}{1-\\sin x}=\\tan x+\\sec x$'],
  steps: ['$\\dfrac{1+\\sin x}{\\cos^{2}x}=\\sec^{2}x+\\sec x\\tan x$',
          '$\\left[\\tan x+\\sec x\\right]_{-\\pi/4}^{\\pi/4}=(1+\\sqrt2)-(-1+\\sqrt2)$',
          '$=2$'] });

add('hard', '역삼각 치환', '1/(x*sqrt(x^2-2))', 'acos(sqrt(2)/x)/sqrt(2)',
  { domain: [1.6, 4.0],
  hints: ['$\\int\\dfrac{dx}{x\\sqrt{x^{2}-a^{2}}}=\\dfrac1a\\operatorname{arcsec}\\dfrac xa$ 다.',
          '$\\operatorname{arcsec}u=\\arccos\\dfrac1u$'],
  steps: ['$a=\\sqrt2$ 로 놓고 표준형을 쓴다',
          '$=\\dfrac{1}{\\sqrt2}\\arccos\\dfrac{\\sqrt2}{x}$'] });


// --- 2014 -----------------------------------------------------------

addDef('easy', '로그 적분', 'ln(x^2)', '2',
  { lo: '1', hi: 'e',
  hints: ['$\\ln(x^{2})=2\\ln x$ 다.',
          '$\\int\\ln x\\,dx=x\\ln x-x$'],
  steps: ['$2\\left[x\\ln x-x\\right]_{1}^{e}$', '$=2\\left[(e-e)-(0-1)\\right]=2$'] });

addDef('medium', '미적분 기본정리', '(1-2*x)*e^(1+x-x^2)', '-e',
  { lo: '0', hi: 'inf',
  hints: ['피적분함수가 통째로 어떤 함수의 도함수다.',
          '$\\left(e^{1+x-x^{2}}\\right)\'=(1-2x)e^{1+x-x^{2}}$'],
  steps: ['$\\left[e^{1+x-x^{2}}\\right]_{0}^{\\infty}$',
          '위끝은 $0$, 아래끝은 $e$',
          '$=-e$'] });

addDef('hard', '무한 중첩 근호', '(1+sqrt(1+4*x))/2', '19/6',
  { lo: '0', hi: '2',
  hints: ['$y=\\sqrt{x+\\sqrt{x+\\cdots}}$ 는 $y^{2}=x+y$ 를 만족한다.',
          '양수 해는 $y=\\dfrac{1+\\sqrt{1+4x}}{2}$ 다.'],
  steps: ['$y^{2}=x+y\\Rightarrow y=\\dfrac{1+\\sqrt{1+4x}}{2}$',
          '$\\dfrac12\\left[x+\\dfrac{(1+4x)^{3/2}}{6}\\right]_{0}^{2}$',
          '$=\\dfrac{19}{6}$'] });

add('hard', '거듭제곱근 치환', 'sqrt(x)*e^sqrt(x)', '2*e^sqrt(x)*(x-2*sqrt(x)+2)',
  { domain: D.pos,
  hints: ['$u=\\sqrt x$ 로 두면 $dx=2u\\,du$ 다.',
          '$2\\displaystyle\\int u^{2}e^{u}du$ 는 부분적분 두 번이다.'],
  steps: ['$u=\\sqrt x\\Rightarrow2\\displaystyle\\int u^{2}e^{u}du$',
          '$\\int u^{2}e^{u}du=e^{u}(u^{2}-2u+2)$',
          '$=2e^{\\sqrt x}\\left(x-2\\sqrt x+2\\right)$'] });

add('medium', '곱-합 공식', 'sin(2*x)*cos(3*x)', '-cos(5*x)/10+cos(x)/2',
  { domain: D.trigW,
  hints: ['$\\sin A\\cos B=\\dfrac{\\sin(A+B)+\\sin(A-B)}{2}$',
          '$=\\dfrac{\\sin5x-\\sin x}{2}$'],
  steps: ['곱을 합으로 바꾼다', '$=-\\dfrac{\\cos5x}{10}+\\dfrac{\\cos x}{2}$'] });

addDef('monster', '절댓값 나누기', '|1+2*sin(x)|', '2*pi/3+4*sqrt(3)',
  { lo: '0', hi: '2*pi',
  hints: ['$1+2\\sin x=0$ 이 되는 곳은 $x=\\dfrac{7\\pi}{6},\\dfrac{11\\pi}{6}$ 다.',
          '그 사이에서만 음수이므로 그 조각의 부호를 뒤집는다.'],
  steps: ['$\\int_{0}^{2\\pi}(1+2\\sin x)dx=2\\pi$',
          '음수 구간의 적분은 $\\dfrac{2\\pi}{3}-2\\sqrt3$',
          '$\\int|f|=2\\pi-2\\left(\\dfrac{2\\pi}{3}-2\\sqrt3\\right)=\\dfrac{2\\pi}{3}+4\\sqrt3$'] });

add('monster', '치환적분', 'x*(1-x)^2014', '(1-x)^2016/2016-(1-x)^2015/2015',
  { domain: [-0.0009, 0.0009],
  hints: ['$u=1-x$ 로 두면 $x=1-u$ 다.',
          '$\\int(u^{2015}-u^{2014})du$ 만 남는다.'],
  steps: ['$u=1-x,\\ dx=-du$',
          '$\\int(1-u)u^{2014}(-du)=\\int\\left(u^{2015}-u^{2014}\\right)du$',
          '$=\\dfrac{(1-x)^{2016}}{2016}-\\dfrac{(1-x)^{2015}}{2015}$'] });

addDef('medium', '다항식 나눗셈', 'x^2/(x-1)', '1/2-ln(2)',
  { lo: '-1', hi: '0',
  hints: ['$\\dfrac{x^{2}}{x-1}=x+1+\\dfrac{1}{x-1}$ 다.',
          '$\\left[\\dfrac{x^{2}}{2}+x+\\ln|x-1|\\right]$'],
  steps: ['나눗셈으로 쪼갠다',
          '$\\left[\\dfrac{x^{2}}{2}+x+\\ln|x-1|\\right]_{-1}^{0}$',
          '$=0-\\left(-\\dfrac12+\\ln2\\right)=\\dfrac12-\\ln2$'] });

add('hard', '부분분수', '1/(x^2-15*x-2014)', '(ln(x-53)-ln(x+38))/91',
  { domain: [54.0, 70.0], lnAbs: true,
  hints: ['판별식이 $225+8056=8281=91^{2}$ 이다.',
          '근이 $53$ 과 $-38$ 이므로 $(x-53)(x+38)$ 로 인수분해된다.'],
  steps: ['$x^{2}-15x-2014=(x-53)(x+38)$',
          '$\\dfrac{1}{91}\\left(\\dfrac{1}{x-53}-\\dfrac{1}{x+38}\\right)$',
          '$=\\dfrac{1}{91}\\ln\\left|\\dfrac{x-53}{x+38}\\right|$'] });

add('monster', '미분 되짚기', 'e^x*(ln(1+x^2)-2*(1+x)*atan(x))',
    'e^x*(ln(1+x^2)-2*x*atan(x))',
  { domain: D.all,
  hints: ['$\\int e^{x}(f+f\')dx=e^{x}f$ 꼴을 의심해 보라.',
          '$f=\\ln(1+x^{2})-2x\\arctan x$ 로 두고 $f\'$ 을 계산해 보라.'],
  steps: ['$f=\\ln(1+x^{2})-2x\\arctan x$',
          '$f\'=\\dfrac{2x}{1+x^{2}}-2\\arctan x-\\dfrac{2x}{1+x^{2}}=-2\\arctan x$',
          '$f+f\'=\\ln(1+x^{2})-2(x+1)\\arctan x$ 이므로 $=e^{x}f$'] });

add('hard', '부분적분', 'asin(x)^2', 'x*asin(x)^2+2*sqrt(1-x^2)*asin(x)-2*x',
  { domain: D.unit,
  hints: ['$u=\\arcsin^{2}x,\\ dv=dx$ 로 부분적분한다.',
          '남는 적분에 한 번 더 부분적분을 쓴다.'],
  steps: ['$x\\arcsin^{2}x-\\displaystyle\\int\\dfrac{2x\\arcsin x}{\\sqrt{1-x^{2}}}dx$',
          '두 번째 적분도 부분적분한다',
          '$=x\\arcsin^{2}x+2\\sqrt{1-x^{2}}\\arcsin x-2x$'] });

add('hard', '삼각 치환', 'sqrt(x^2-1)/x', 'sqrt(x^2-1)-acos(1/x)',
  { domain: D.gt1,
  hints: ['$x=\\sec\\theta$ 로 두면 $\\int\\tan^{2}\\theta\\,d\\theta$ 가 된다.',
          '$\\int\\tan^{2}\\theta\\,d\\theta=\\tan\\theta-\\theta$'],
  steps: ['$x=\\sec\\theta$ 치환',
          '$\\tan\\theta=\\sqrt{x^{2}-1},\\ \\theta=\\operatorname{arcsec}x$',
          '$=\\sqrt{x^{2}-1}-\\arccos\\dfrac1x$'] });

add('hard', '부분적분', 'x*sec(4*x)^2', 'x*tan(4*x)/4+ln(cos(4*x))/16',
  { domain: [0.05, 0.35], lnAbs: true,
  hints: ['$u=x,\\ dv=\\sec^{2}(4x)dx$ 로 두면 $v=\\dfrac{\\tan4x}{4}$ 다.',
          '$\\int\\tan4x\\,dx=-\\dfrac{\\ln|\\cos4x|}{4}$'],
  steps: ['부분적분 $\\Rightarrow\\dfrac{x\\tan4x}{4}-\\dfrac14\\displaystyle\\int\\tan4x\\,dx$',
          '$=\\dfrac{x\\tan4x}{4}+\\dfrac{\\ln|\\cos4x|}{16}$'] });

add('hard', '부분분수', '2/(6-11*x+6*x^2-x^3)', '-ln(x-1)+2*ln(x-2)-ln(x-3)',
  { domain: [3.4, 6.0], lnAbs: true,
  hints: ['$x^{3}-6x^{2}+11x-6=(x-1)(x-2)(x-3)$ 이다.',
          '부호에 주의하라 — 분모는 그 값의 $-1$ 배다.'],
  steps: ['$6-11x+6x^{2}-x^{3}=-(x-1)(x-2)(x-3)$',
          '부분분수로 $-\\dfrac{1}{x-1}+\\dfrac{2}{x-2}-\\dfrac{1}{x-3}$',
          '항마다 로그로 적분한다'] });

addDef('monster', '쌍곡선 치환', 'sqrt(x+sqrt(x^2+1))', '2/3',
  { lo: '0', hi: '1/sqrt(3)',
  hints: ['$x=\\sinh t$ 로 두면 $x+\\sqrt{x^{2}+1}=e^{t}$ 다.',
          '피적분함수가 $e^{t/2}$, $dx=\\cosh t\\,dt$ 가 된다.'],
  steps: ['$u=x+\\sqrt{x^{2}+1}$ 로 두면 원시함수가 $\\dfrac{u^{3/2}}{3}-u^{-1/2}$',
          '$x=\\dfrac{1}{\\sqrt3}$ 에서 $u=\\sqrt3$ 이라 값이 $0$',
          '$x=0$ 에서 $u=1$ 이라 $-\\dfrac23$, 따라서 $\\dfrac23$'] });

addDef('hard', '주기 나누기', '1/(2+cos(x))', '7*pi/(3*sqrt(3))',
  { lo: '0', hi: '5*pi/2',
  hints: ['주기가 $2\\pi$ 이므로 $\\int_{0}^{2\\pi}$ 와 $\\int_{0}^{\\pi/2}$ 로 나눈다.',
          '$\\int\\dfrac{dx}{2+\\cos x}=\\dfrac{2}{\\sqrt3}\\arctan\\dfrac{\\tan(x/2)}{\\sqrt3}$'],
  steps: ['$\\int_{0}^{2\\pi}=\\dfrac{2\\pi}{\\sqrt3}$',
          '$\\int_{0}^{\\pi/2}=\\dfrac{\\pi}{3\\sqrt3}$',
          '합하면 $\\dfrac{7\\pi}{3\\sqrt3}$'] });


// --- 2015 -----------------------------------------------------------

add('medium', '항등식 정리', 'cos(x)^4-sin(x)^4', 'sin(2*x)/2',
  { domain: D.trigW,
  hints: ['$a^{2}-b^{2}=(a-b)(a+b)$ 를 $a=\\cos^{2}x,\\ b=\\sin^{2}x$ 에 쓴다.',
          '$\\cos^{2}x+\\sin^{2}x=1$ 이므로 $\\cos2x$ 만 남는다.'],
  steps: ['$\\cos^{4}x-\\sin^{4}x=\\cos^{2}x-\\sin^{2}x=\\cos2x$',
          '$=\\dfrac{\\sin2x}{2}$'] });

add('medium', '치환적분', 'x/sqrt(2+4*x)', '(2+4*x)^(3/2)/24-sqrt(2+4*x)/4',
  { domain: D.poly,
  hints: ['$u=2+4x$ 로 두면 $x=\\dfrac{u-2}{4}$ 다.',
          '$\\dfrac{1}{16}\\displaystyle\\int\\left(u^{1/2}-2u^{-1/2}\\right)du$'],
  steps: ['$u=2+4x$ 치환',
          '$=\\dfrac{u^{3/2}}{24}-\\dfrac{u^{1/2}}{4}$'] });

addDef('medium', '치환적분', 'cos(sqrt(x))/sqrt(x)', '2*sin(2*sqrt(2))',
  { lo: '0', hi: '8',
  hints: ['$u=\\sqrt x$ 로 두면 $\\dfrac{dx}{\\sqrt x}=2\\,du$ 다.',
          '$\\sqrt8=2\\sqrt2$'],
  steps: ['$u=\\sqrt x\\Rightarrow2\\displaystyle\\int_{0}^{2\\sqrt2}\\cos u\\,du$',
          '$=2\\sin\\left(2\\sqrt2\\right)$'] });

addDef('medium', '항등식 정리', 'e^sin(x)/(tan(x)*csc(x))', 'e-1',
  { lo: '0', hi: 'pi/2',
  hints: ['$\\tan x\\csc x=\\dfrac{\\sin x}{\\cos x}\\cdot\\dfrac{1}{\\sin x}=\\sec x$ 다.',
          '남는 것은 $e^{\\sin x}\\cos x$ 다.'],
  steps: ['$\\dfrac{e^{\\sin x}}{\\sec x}=e^{\\sin x}\\cos x$',
          '$\\left[e^{\\sin x}\\right]_{0}^{\\pi/2}=e-1$'] });

addDef('medium', '부분적분', 'x*ln(x)^2', '(e^2-1)/4',
  { lo: '1', hi: 'e',
  hints: ['$u=\\ln^{2}x,\\ dv=x\\,dx$ 로 부분적분한다.',
          '남는 $\\int x\\ln x\\,dx$ 도 부분적분이다.'],
  steps: ['$\\dfrac{x^{2}}{2}\\ln^{2}x-\\displaystyle\\int x\\ln x\\,dx$',
          '$=\\dfrac{x^{2}}{2}\\ln^{2}x-\\dfrac{x^{2}}{2}\\ln x+\\dfrac{x^{2}}{4}$',
          '$=\\dfrac{e^{2}-1}{4}$'] });

add('hard', '거듭제곱근 치환', '1/(5+4*sqrt(x)+x)',
    'ln((sqrt(x)+2)^2+1)-4*atan(sqrt(x)+2)',
  { domain: D.pos,
  hints: ['$u=\\sqrt x$ 로 두면 분모가 $u^{2}+4u+5=(u+2)^{2}+1$ 이다.',
          '분자 $2u$ 를 $2(u+2)-4$ 로 쪼갠다.'],
  steps: ['$u=\\sqrt x\\Rightarrow\\displaystyle\\int\\dfrac{2u\\,du}{(u+2)^{2}+1}$',
          '$=\\ln\\left((u+2)^{2}+1\\right)-4\\arctan(u+2)$'] });

add('easy', '지수함수', '2015^x', '2015^x/ln(2015)',
  { domain: [-1.0, 1.5],
  hints: ['$a^{x}=e^{x\\ln a}$ 로 고쳐 쓴다.',
          '$\\int a^{x}dx=\\dfrac{a^{x}}{\\ln a}$'],
  steps: ['$2015^{x}=e^{x\\ln2015}$', '$=\\dfrac{2015^{x}}{\\ln2015}$'] });

addDef('hard', '부분분수', 'x/((x-3)*(x+5)^2)', '1/28-3*ln(21/5)/64',
  { lo: '0', hi: '2',
  hints: ['중근이 있으므로 $\\dfrac{A}{x-3}+\\dfrac{B}{x+5}+\\dfrac{C}{(x+5)^{2}}$ 로 둔다.',
          '$A=\\dfrac{3}{64},\\ B=-\\dfrac{3}{64},\\ C=\\dfrac58$'],
  steps: ['부분분수로 쪼갠다',
          '$\\left[\\dfrac{3}{64}\\ln\\left|\\dfrac{x-3}{x+5}\\right|-\\dfrac{5}{8(x+5)}\\right]_{0}^{2}$',
          '$=\\dfrac{1}{28}-\\dfrac{3}{64}\\ln\\dfrac{21}{5}$'] });

add('hard', '로그 치환', 'ln(1+ln(x))/x', '(1+ln(x))*ln(1+ln(x))-(1+ln(x))',
  { domain: [0.6, 3.0],
  hints: ['$u=1+\\ln x$ 로 두면 $du=\\dfrac{dx}{x}$ 다.',
          '$\\int\\ln u\\,du=u\\ln u-u$'],
  steps: ['$u=1+\\ln x$ 치환',
          '$=u\\ln u-u=(1+\\ln x)\\ln(1+\\ln x)-(1+\\ln x)$'] });

add('medium', '쌍곡역함수', '1/sqrt(x^2+25)', 'asinh(x/5)',
  { domain: D.all,
  hints: ['$\\int\\dfrac{dx}{\\sqrt{x^{2}+a^{2}}}=\\operatorname{arsinh}\\dfrac xa$ 다.',
          '$=\\ln\\left(x+\\sqrt{x^{2}+a^{2}}\\right)$ 로 써도 같다.'],
  steps: ['$x=5\\sinh t$ 치환', '$=\\operatorname{arsinh}\\dfrac x5$'] });

addDef('hard', '미분 되짚기', '(ln(x)^2-1)/(x*ln(x)^2)', '2-ln(2)-1/ln(2)',
  { lo: '2', hi: 'e',
  hints: ['$\\dfrac{\\ln^{2}x-1}{x\\ln^{2}x}=\\dfrac1x-\\dfrac{1}{x\\ln^{2}x}$ 로 쪼갠다.',
          '뒤쪽은 $u=\\ln x$ 로 두면 $\\int u^{-2}du$ 다.'],
  steps: ['원시함수는 $\\ln x+\\dfrac{1}{\\ln x}$',
          '$\\left[\\ln x+\\dfrac{1}{\\ln x}\\right]_{2}^{e}=2-\\ln2-\\dfrac{1}{\\ln2}$'] });

add('monster', '부분적분', 'e^(3*x)*atan(e^x)',
    'e^(3*x)*atan(e^x)/3-e^(2*x)/6+ln(1+e^(2*x))/6',
  { domain: [-1.0, 1.5],
  hints: ['$u=e^{x}$ 로 두면 $\\displaystyle\\int u^{2}\\arctan u\\,du$ 가 된다.',
          '부분적분 뒤 남는 $\\displaystyle\\int\\dfrac{u^{3}}{1+u^{2}}du$ 는 나눗셈으로 푼다.'],
  steps: ['$u=e^{x}$ 치환 후 부분적분',
          '$\\dfrac{u^{3}}{3}\\arctan u-\\dfrac13\\displaystyle\\int\\dfrac{u^{3}}{1+u^{2}}du$',
          '$=\\dfrac{e^{3x}\\arctan(e^{x})}{3}-\\dfrac{e^{2x}}{6}+\\dfrac{\\ln(1+e^{2x})}{6}$'] });

addDef('monster', '절댓값 나누기', '|x-1|/(|x-2|+|x-3|)', '2+3*ln(27/5)/4',
  { lo: '0', hi: '4',
  hints: ['$x=1,2,3$ 에서 절댓값의 부호가 바뀐다 — 네 구간으로 쪼갠다.',
          '$[2,3]$ 에서는 분모가 $1$ 로 딱 떨어진다.'],
  steps: ['$[0,1],[1,2]$ 에서 분모는 $5-2x$, $[2,3]$ 에서는 $1$, $[3,4]$ 에서는 $2x-5$',
          '조각마다 적분해 더한다',
          '$=2+\\dfrac{3}{4}\\ln\\dfrac{27}{5}$'] });

addDef('monster', '주기 대칭', '1/(sin(x)^4+cos(x)^4)', '2*pi*sqrt(2)',
  { lo: '0', hi: '2*pi',
  hints: ['$\\sin^{4}x+\\cos^{4}x=1-\\dfrac{\\sin^{2}2x}{2}$ 다.',
          '주기가 $\\dfrac\\pi2$ 이므로 $4\\displaystyle\\int_{0}^{\\pi/2}$ 로 줄인다.'],
  steps: ['$1-\\dfrac{\\sin^{2}2x}{2}$ 로 고친다',
          '$\\int_{0}^{\\pi/2}\\dfrac{d\\theta}{1-k\\sin^{2}\\theta}=\\dfrac{\\pi}{2\\sqrt{1-k}}$ 에 $k=\\dfrac12$',
          '$=2\\sqrt2\\,\\pi$'] });

add('hard', '지수 유리식', '(1+e^x)/(1-e^x)', 'x-2*ln(1-e^x)',
  { domain: [-2.2, -0.25], lnAbs: true,
  hints: ['$\\dfrac{1+e^{x}}{1-e^{x}}=-1+\\dfrac{2}{1-e^{x}}$ 로 쪼갠다.',
          '$\\dfrac{1}{1-e^{x}}=1+\\dfrac{e^{x}}{1-e^{x}}$'],
  steps: ['두 번 쪼갠다',
          '$\\int\\dfrac{dx}{1-e^{x}}=x-\\ln\\left|1-e^{x}\\right|$',
          '$=x-2\\ln\\left|1-e^{x}\\right|$'] });

add('medium', '점화식', 'tan(x)^4', 'tan(x)^3/3-tan(x)+x',
  { domain: D.trig,
  hints: ['$\\tan^{4}x=\\tan^{2}x(\\sec^{2}x-1)$ 로 쪼갠다.',
          '$\\int\\tan^{2}x\\,dx=\\tan x-x$'],
  steps: ['$\\tan^{2}x\\sec^{2}x-\\tan^{2}x$',
          '$=\\dfrac{\\tan^{3}x}{3}-(\\tan x-x)$'] });

add('medium', '항등식 정리', 'sin(x)*tan(x)^2', '1/cos(x)+cos(x)',
  { domain: D.trig,
  hints: ['$\\tan^{2}x=\\sec^{2}x-1$ 로 바꾼다.',
          '$\\displaystyle\\int\\dfrac{\\sin x}{\\cos^{2}x}dx=\\sec x$'],
  steps: ['$\\sin x\\sec^{2}x-\\sin x$',
          '$=\\sec x+\\cos x$'] });

add('medium', '치환적분', '(x+1)/(x^2+2*x+3)', 'ln(x^2+2*x+3)/2',
  { domain: D.all,
  hints: ['분모의 도함수가 $2x+2$ 다.',
          '분자는 그 절반이다.'],
  steps: ['$u=x^{2}+2x+3$ 치환', '$=\\dfrac{\\ln(x^{2}+2x+3)}{2}$'] });


// --- 2016 -----------------------------------------------------------

add('medium', '쌍곡선함수', 'tanh(x)', 'ln(cosh(x))',
  { domain: D.hyp,
  hints: ['$\\tanh x=\\dfrac{\\sinh x}{\\cosh x}$ 이고 분모의 도함수가 분자다.',
          '$\\int\\tanh x\\,dx=\\ln\\cosh x$'],
  steps: ['$u=\\cosh x$ 치환', '$=\\ln\\cosh x$'] });

addDef('hard', '절댓값 나누기', '|x^3-x|', '113',
  { lo: '-4', hi: '4',
  hints: ['$x^{3}-x$ 는 홀함수라 $|x^{3}-x|$ 는 짝함수다 — 절반만 계산하면 된다.',
          '$[0,1]$ 에서는 음수, $[1,4]$ 에서는 양수다.'],
  steps: ['$2\\left(\\int_{0}^{1}(x-x^{3})dx+\\int_{1}^{4}(x^{3}-x)dx\\right)$',
          '$=2\\left(\\dfrac14+\\dfrac{225}{4}\\right)$',
          '$=113$'] });

addDef('easy', '로그 법칙', 'ln(sqrt(x))', '1/2',
  { lo: '1', hi: 'e',
  hints: ['$\\ln\\sqrt x=\\dfrac{\\ln x}{2}$ 다.',
          '$\\int_{1}^{e}\\ln x\\,dx=1$'],
  steps: ['$\\dfrac12\\displaystyle\\int_{1}^{e}\\ln x\\,dx$', '$=\\dfrac12$'] });

add('hard', '치환적분', 'e^(e^x+e^(-x)+x)-e^(e^x+e^(-x)-x)', 'e^(e^x+e^(-x))',
  { domain: [-1.2, 1.2],
  hints: ['$e^{x}$ 를 공통으로 묶으면 $e^{e^{x}+e^{-x}}\\left(e^{x}-e^{-x}\\right)$ 다.',
          '$u=e^{x}+e^{-x}$ 로 두면 $du=(e^{x}-e^{-x})dx$ 다.'],
  steps: ['공통 인수로 묶는다',
          '$u=e^{x}+e^{-x}$ 치환 $\\Rightarrow\\int e^{u}du$',
          '$=e^{e^{x}+e^{-x}}$'] });

add('medium', '이중 로그 치환', 'ln(ln(x))/(x*ln(x))', 'ln(ln(x))^2/2',
  { domain: D.lnln,
  hints: ['$u=\\ln(\\ln x)$ 로 두면 $du=\\dfrac{dx}{x\\ln x}$ 다.',
          '$\\int u\\,du=\\dfrac{u^{2}}{2}$'],
  steps: ['$u=\\ln(\\ln x)$ 치환', '$=\\dfrac{\\ln^{2}(\\ln x)}{2}$'] });

addDef('medium', '항등식 정리', '1/(1+tan(x)^2)', 'pi/6+sqrt(3)/8',
  { lo: '0', hi: 'pi/3',
  hints: ['$1+\\tan^{2}x=\\sec^{2}x$ 이므로 피적분함수는 $\\cos^{2}x$ 다.',
          '$\\int\\cos^{2}x\\,dx=\\dfrac x2+\\dfrac{\\sin2x}{4}$'],
  steps: ['$\\cos^{2}x$ 로 정리',
          '$\\left[\\dfrac x2+\\dfrac{\\sin2x}{4}\\right]_{0}^{\\pi/3}=\\dfrac{\\pi}{6}+\\dfrac{\\sqrt3}{8}$'] });

add('medium', '곱의 미분 되짚기', 'e^x*cos(x)-e^x*sin(x)', 'e^x*cos(x)',
  { domain: D.all,
  hints: ['$(e^{x}\\cos x)\'$ 를 곱의 미분법으로 계산해 보라.',
          '$e^{x}\\cos x-e^{x}\\sin x$ 가 그대로 나온다.'],
  steps: ['$(e^{x}\\cos x)\'=e^{x}\\cos x-e^{x}\\sin x$', '$=e^{x}\\cos x$'] });

addDef('medium', '치환 후 부분적분', 'x^3*e^(-x^2)', '1/2',
  { lo: '0', hi: 'inf',
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\displaystyle\\int_{0}^{\\infty}ue^{-u}du$ 다.',
          '$\\int_{0}^{\\infty}ue^{-u}du=\\Gamma(2)=1$'],
  steps: ['$u=x^{2}$ 치환', '$=\\dfrac12\\Gamma(2)=\\dfrac12$'] });

add('hard', '곱의 미분 되짚기', '(2*x*e^(x^2)+1)*cos(x)-(e^(x^2)+x)*sin(x)',
    '(e^(x^2)+x)*cos(x)',
  { domain: [-1.2, 1.2],
  hints: ['$f=e^{x^{2}}+x$ 로 두면 $f\'=2xe^{x^{2}}+1$ 이다.',
          '$f\'\\cos x-f\\sin x=(f\\cos x)\'$'],
  steps: ['$f=e^{x^{2}}+x$ 로 두면 피적분함수는 $f\'\\cos x-f\\sin x$',
          '$=(f\\cos x)\'$',
          '$=\\left(e^{x^{2}}+x\\right)\\cos x$'] });

add('hard', '전개', '(1+x^(1/2)+x^(1/3))*(1+x^(-1/2)+x^(-1/3))',
    '3*x+2*sqrt(x)+(3/2)*x^(2/3)+(2/3)*x^(3/2)+(3/4)*x^(4/3)+(6/7)*x^(7/6)+(6/5)*x^(5/6)',
  { domain: D.pos,
  hints: ['괄호를 그냥 전개하면 지수가 $\\pm\\frac12,\\pm\\frac13,\\pm\\frac16$ 인 항들이 나온다.',
          '상수항은 $1$ 이 세 번 나와 $3$ 이다.'],
  steps: ['전개하면 $3+x^{1/2}+x^{1/3}+x^{1/6}+x^{-1/2}+x^{-1/3}+x^{-1/6}$',
          '항마다 거듭제곱 법칙을 쓴다'] });

add('medium', '이중 치환', 'sin(sin(x))*cos(sin(x))*cos(x)', 'sin(sin(x))^2/2',
  { domain: D.trigW,
  hints: ['$u=\\sin x$ 로 두면 $\\int\\sin u\\cos u\\,du$ 다.',
          '다시 $v=\\sin u$ 로 두면 끝난다.'],
  steps: ['$u=\\sin x$ 치환', '$\\int\\sin u\\cos u\\,du=\\dfrac{\\sin^{2}u}{2}$',
          '$=\\dfrac{\\sin^{2}(\\sin x)}{2}$'] });

add('hard', '몫의 미분 되짚기', '(cos(x)+sin(x))/x^2+(sin(x)-cos(x))/x',
    '-(cos(x)+sin(x))/x',
  { domain: [0.4, 2.6],
  hints: ['답이 $\\dfrac{f}{x}$ 꼴이라고 짐작하고 몫의 미분법을 써 보라.',
          '$\\left(-\\dfrac{\\cos x+\\sin x}{x}\\right)\'$ 를 계산해 보라.'],
  steps: ['$\\left(-\\dfrac{\\cos x+\\sin x}{x}\\right)\'=\\dfrac{\\cos x+\\sin x}{x^{2}}-\\dfrac{\\cos x-\\sin x}{x}$',
          '피적분함수와 같다'] });

add('medium', '치환적분', 'x^3*sqrt(x^2+1)', '(x^2+1)^(5/2)/5-(x^2+1)^(3/2)/3',
  { domain: D.all,
  hints: ['$u=x^{2}+1$ 로 두면 $x^{2}=u-1$ 이다.',
          '$x^{3}dx=x^{2}\\cdot x\\,dx=\\dfrac{(u-1)du}{2}$'],
  steps: ['$u=x^{2}+1$ 치환',
          '$\\dfrac12\\int\\left(u^{3/2}-u^{1/2}\\right)du$',
          '$=\\dfrac{u^{5/2}}{5}-\\dfrac{u^{3/2}}{3}$'] });

add('hard', '완전제곱', 'x/(x^4+x^2+1)', 'atan((2*x^2+1)/sqrt(3))/sqrt(3)',
  { domain: D.poly,
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\displaystyle\\int\\dfrac{du}{u^{2}+u+1}$ 다.',
          '$u^{2}+u+1=\\left(u+\\dfrac12\\right)^{2}+\\dfrac34$'],
  steps: ['$u=x^{2}$ 치환 후 완전제곱',
          '$=\\dfrac{1}{\\sqrt3}\\arctan\\dfrac{2x^{2}+1}{\\sqrt3}$'] });

add('monster', '이중 지수', 'e^(e^(2016*x)+6048*x)',
    'e^(e^(2016*x))*(e^(4032*x)-2*e^(2016*x)+2)/2016',
  { domain: [-0.001, 0.0005],
  hints: ['$e^{6048x}=\\left(e^{2016x}\\right)^{3}$ 임을 먼저 알아채라.',
          '$u=e^{2016x}$ 로 두면 $\\dfrac{1}{2016}\\displaystyle\\int u^{2}e^{u}du$ 가 된다.'],
  steps: ['$u=e^{2016x},\\ du=2016u\\,dx$',
          '$\\dfrac{1}{2016}\\int u^{2}e^{u}du=\\dfrac{e^{u}(u^{2}-2u+2)}{2016}$',
          '$u=e^{2016x}$ 를 되돌린다'] });

addDef('medium', '반각 공식', '(1-cos(x))/sin(x)', 'ln(3/2)',
  { lo: 'pi/3', hi: 'pi/2',
  hints: ['$\\dfrac{1-\\cos x}{\\sin x}=\\tan\\dfrac x2$ 다.',
          '$\\int\\tan\\dfrac x2dx=-2\\ln\\left|\\cos\\dfrac x2\\right|$'],
  steps: ['반각 공식으로 $\\tan\\dfrac x2$',
          '$\\left[-2\\ln\\cos\\dfrac x2\\right]_{\\pi/3}^{\\pi/2}=\\ln2-\\ln\\dfrac43$',
          '$=\\ln\\dfrac32$'] });

add('hard', '부분분수', '1/(1-x+x^2-x^3)', '-ln(1-x)/2+ln(1+x^2)/4+atan(x)/2',
  { domain: [-1.5, 0.7], lnAbs: true,
  hints: ['분모를 묶어 보라: $(1-x)(1+x^{2})$ 다.',
          '$\\dfrac{1}{(1-x)(1+x^{2})}=\\dfrac{1}{2(1-x)}+\\dfrac{x+1}{2(1+x^{2})}$'],
  steps: ['$1-x+x^{2}-x^{3}=(1-x)(1+x^{2})$',
          '부분분수로 쪼갠다',
          '$=-\\dfrac{\\ln|1-x|}{2}+\\dfrac{\\ln(1+x^{2})}{4}+\\dfrac{\\arctan x}{2}$'] });

addDef('hard', '지수 치환', '1/(2+cosh(x))', 'ln(2+sqrt(3))/sqrt(3)',
  { lo: '0', hi: 'inf',
  hints: ['$t=e^{x}$ 로 두면 $\\displaystyle\\int_{1}^{\\infty}\\dfrac{2\\,dt}{t^{2}+4t+1}$ 다.',
          '$t^{2}+4t+1=(t+2)^{2}-3$'],
  steps: ['$t=e^{x}$ 치환 후 완전제곱',
          '$\\dfrac{1}{\\sqrt3}\\ln\\dfrac{t+2-\\sqrt3}{t+2+\\sqrt3}$ 가 원시함수',
          '$=\\dfrac{\\ln(2+\\sqrt3)}{\\sqrt3}$'] });

// --- 2017 -----------------------------------------------------------

add('easy', '치환적분', 'x^2/sqrt(x^3+2)', '(2/3)*sqrt(x^3+2)',
  { domain: D.poly,
  hints: ['$u=x^{3}+2$ 로 두면 $du=3x^{2}dx$ 다.',
          '$\\int u^{-1/2}du=2\\sqrt u$'],
  steps: ['$u=x^{3}+2$ 치환', '$=\\dfrac23\\sqrt{x^{3}+2}$'] });

addDef('medium', '부분적분', 'ln(x)/x^2', '1',
  { lo: '1', hi: 'inf',
  hints: ['$u=\\ln x,\\ dv=x^{-2}dx$ 로 부분적분한다.',
          '원시함수는 $-\\dfrac{\\ln x+1}{x}$ 다.'],
  steps: ['부분적분 $\\Rightarrow-\\dfrac{\\ln x}{x}-\\displaystyle\\int-\\dfrac{1}{x^{2}}dx$',
          '$=-\\dfrac{\\ln x+1}{x}$, 위끝은 $0$',
          '$=1$'] });

add('medium', '치환 후 부분적분', 'x^3*e^(x^2)', '(x^2-1)*e^(x^2)/2',
  { domain: [-1.4, 1.4],
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\displaystyle\\int ue^{u}du$ 다.',
          '$\\int ue^{u}du=(u-1)e^{u}$'],
  steps: ['$u=x^{2}$ 치환', '$=\\dfrac{(x^{2}-1)e^{x^{2}}}{2}$'] });

addDef('medium', '역삼각 치환', '1/(x*sqrt(x^2-1))', 'pi/3',
  { lo: '1', hi: '2',
  hints: ['$\\int\\dfrac{dx}{x\\sqrt{x^{2}-1}}=\\operatorname{arcsec}x$ 다.',
          '$\\operatorname{arcsec}2=\\dfrac{\\pi}{3}$'],
  steps: ['$\\left[\\operatorname{arcsec}x\\right]_{1}^{2}$', '$=\\dfrac{\\pi}{3}-0=\\dfrac{\\pi}{3}$'] });

addDef('medium', '부분분수', '1/(x*(x^2+1))', 'ln(2)/2',
  { lo: '1', hi: 'inf',
  hints: ['$\\dfrac{1}{x(x^{2}+1)}=\\dfrac1x-\\dfrac{x}{x^{2}+1}$ 이다.',
          '원시함수는 $\\ln\\dfrac{x}{\\sqrt{x^{2}+1}}$ 다.'],
  steps: ['부분분수로 쪼갠다',
          '$\\left[\\ln\\dfrac{x}{\\sqrt{x^{2}+1}}\\right]_{1}^{\\infty}$',
          '$=0-\\ln\\dfrac{1}{\\sqrt2}=\\dfrac{\\ln2}{2}$'] });

addDef('hard', '가우스 적분', 'e^(-2*x^2-5*x-3)', 'e^(1/8)*sqrt(pi/2)',
  { lo: '-inf', hi: 'inf',
  hints: ['지수를 완전제곱하라: $-2x^{2}-5x-3=-2\\left(x+\\dfrac54\\right)^{2}+\\dfrac18$',
          '$\\int_{-\\infty}^{\\infty}e^{-au^{2}}du=\\sqrt{\\dfrac{\\pi}{a}}$'],
  steps: ['지수를 완전제곱한다',
          '$e^{1/8}\\displaystyle\\int_{-\\infty}^{\\infty}e^{-2u^{2}}du$',
          '$=e^{1/8}\\sqrt{\\dfrac{\\pi}{2}}$'] });

add('hard', '거듭제곱근 치환', 'sin(sqrt(x))', '2*sin(sqrt(x))-2*sqrt(x)*cos(sqrt(x))',
  { domain: D.pos,
  hints: ['$u=\\sqrt x$ 로 두면 $dx=2u\\,du$ 다.',
          '$2\\displaystyle\\int u\\sin u\\,du$ 는 부분적분이다.'],
  steps: ['$u=\\sqrt x\\Rightarrow2\\displaystyle\\int u\\sin u\\,du$',
          '$=2(\\sin u-u\\cos u)$',
          '$=2\\sin\\sqrt x-2\\sqrt x\\cos\\sqrt x$'] });

addDef('hard', '삼각 치환', '1/(x+1/x)^2', 'pi/4',
  { lo: '0', hi: 'inf',
  hints: ['$\\dfrac{1}{(x+1/x)^{2}}=\\dfrac{x^{2}}{(x^{2}+1)^{2}}$ 로 고친다.',
          '$x=\\tan\\theta$ 로 두면 $\\int\\sin^{2}\\theta\\,d\\theta$ 다.'],
  steps: ['$\\dfrac{x^{2}}{(x^{2}+1)^{2}}$ 로 정리',
          '$x=\\tan\\theta\\Rightarrow\\int_{0}^{\\pi/2}\\sin^{2}\\theta\\,d\\theta$',
          '$=\\dfrac{\\pi}{4}$'] });

add('hard', '몫의 미분 되짚기', '(2+x)*e^(-x)/x^3', '-e^(-x)/x^2',
  { domain: [0.4, 2.6],
  hints: ['답이 $\\dfrac{e^{-x}}{x^{2}}$ 꼴이라고 짐작하고 미분해 보라.',
          '$\\left(-\\dfrac{e^{-x}}{x^{2}}\\right)\'=\\dfrac{e^{-x}}{x^{2}}+\\dfrac{2e^{-x}}{x^{3}}$'],
  steps: ['$\\left(-e^{-x}x^{-2}\\right)\'=e^{-x}x^{-2}+2e^{-x}x^{-3}$',
          '$=\\dfrac{(x+2)e^{-x}}{x^{3}}$'] });

addDef('medium', '베타 함수', '1/sqrt(x*(1-x))', 'pi',
  { lo: '0', hi: '1',
  hints: ['$x=\\sin^{2}\\theta$ 로 두면 피적분함수가 상수가 된다.',
          '$\\sqrt{x(1-x)}=\\sin\\theta\\cos\\theta$, $dx=2\\sin\\theta\\cos\\theta\\,d\\theta$'],
  steps: ['$x=\\sin^{2}\\theta$ 치환',
          '$\\int_{0}^{\\pi/2}2\\,d\\theta=\\pi$'] });

addDef('hard', '급수 전개', 'tanh(x)/e^x', 'pi/2-1',
  { lo: '0', hi: 'inf',
  hints: ['$\\tanh x=1-\\dfrac{2}{e^{2x}+1}$ 로 쪼갠다.',
          '남는 적분은 $t=e^{-x}$ 로 두면 $2\\displaystyle\\int_{0}^{1}\\dfrac{t^{2}}{1+t^{2}}dt$ 다.'],
  steps: ['$\\int_{0}^{\\infty}e^{-x}dx=1$',
          '$\\int_{0}^{\\infty}\\dfrac{2e^{-x}}{e^{2x}+1}dx=2\\left(1-\\dfrac{\\pi}{4}\\right)$',
          '$=1-\\left(2-\\dfrac{\\pi}{2}\\right)=\\dfrac{\\pi}{2}-1$'] });

addDef('hard', '반각 공식', 'sqrt(1+sin(x))', '2',
  { lo: '0', hi: 'pi/2',
  hints: ['$1+\\sin x=\\left(\\sin\\dfrac x2+\\cos\\dfrac x2\\right)^{2}$ 다.',
          '구간에서 그 합은 양수라 근호가 그대로 벗겨진다.'],
  steps: ['$\\sqrt{1+\\sin x}=\\sin\\dfrac x2+\\cos\\dfrac x2$',
          '$\\left[-2\\cos\\dfrac x2+2\\sin\\dfrac x2\\right]_{0}^{\\pi/2}$',
          '$=0-(-2)=2$'] });

addDef('monster', '가우스 적분', 'sin(x+pi/4)^2/e^(x^2)', 'sqrt(pi)/2',
  { lo: '-inf', hi: 'inf',
  hints: ['$\\sin^{2}\\left(x+\\dfrac\\pi4\\right)=\\dfrac{1+\\sin2x}{2}$ 다.',
          '$e^{-x^{2}}\\sin2x$ 는 홀함수라 대칭 구간에서 사라진다.'],
  steps: ['$\\dfrac{1+\\sin2x}{2}$ 로 고친다',
          '홀함수 항은 $0$',
          '$=\\dfrac12\\sqrt\\pi$'] });

addDef('monster', '완전제곱 치환', '3*x^2*(x^3+1)^2*e^(-x^6-2*x^3)', 'e*sqrt(pi)/2',
  { lo: '-inf', hi: 'inf',
  hints: ['지수를 완전제곱하라: $-x^{6}-2x^{3}=-(x^{3}+1)^{2}+1$',
          '$u=x^{3}+1$ 로 두면 $du=3x^{2}dx$ 다.'],
  steps: ['$e\\displaystyle\\int_{-\\infty}^{\\infty}u^{2}e^{-u^{2}}du$ 로 바뀐다',
          '$\\int_{-\\infty}^{\\infty}u^{2}e^{-u^{2}}du=\\dfrac{\\sqrt\\pi}{2}$',
          '$=\\dfrac{e\\sqrt\\pi}{2}$'] });

addDef('monster', '킹 성질', '1/(1+tan(x)^2017)', 'pi/4',
  { lo: '0', hi: 'pi/2',
  hints: ['$x\\to\\dfrac\\pi2-x$ 를 넣으면 $\\tan$ 이 $\\cot$ 으로 바뀐다.',
          '원래 식과 더하면 $1$ 이 된다 — 지수는 아무 상관이 없다.'],
  steps: ['$f(x)+f\\left(\\dfrac\\pi2-x\\right)=1$',
          '$2I=\\dfrac{\\pi}{2}$',
          '$I=\\dfrac{\\pi}{4}$'] });

add('hard', '순환 부분적분', 'e^(2*x)*cos(3*x)', 'e^(2*x)*(2*cos(3*x)+3*sin(3*x))/13',
  { domain: [-1.0, 1.5],
  hints: ['부분적분을 두 번 하면 원래 적분이 다시 나온다.',
          '$\\int e^{ax}\\cos bx\\,dx=\\dfrac{e^{ax}(a\\cos bx+b\\sin bx)}{a^{2}+b^{2}}$'],
  steps: ['$a=2,\\ b=3$ 을 공식에 넣는다',
          '$=\\dfrac{e^{2x}(2\\cos3x+3\\sin3x)}{13}$'] });

add('monster', '지수 탑', 'cos(x)^(cos(x)+1)*tan(x)*(1+ln(cos(x)))', '-cos(x)^cos(x)',
  { domain: [0.2, 1.3],
  hints: ['$y=(\\cos x)^{\\cos x}=e^{\\cos x\\ln\\cos x}$ 로 두고 미분해 보라.',
          '$y\'=-y\\sin x\\left(1+\\ln\\cos x\\right)$ 가 나온다.'],
  steps: ['$y=(\\cos x)^{\\cos x}$ 로 두면 $y\'=-y\\sin x(1+\\ln\\cos x)$',
          '피적분함수는 $y\\cos x\\cdot\\dfrac{\\sin x}{\\cos x}(1+\\ln\\cos x)=-y\'$',
          '$=-(\\cos x)^{\\cos x}$'] });


// --- 2018 -----------------------------------------------------------

add('easy', '치환적분', 'e^x/(e^x+2)', 'ln(e^x+2)',
  { domain: D.all,
  hints: ['분모의 도함수가 분자다.', '$u=e^{x}+2$ 치환'],
  steps: ['$u=e^{x}+2$ 치환', '$=\\ln(e^{x}+2)$'] });

add('monster', '무한 중첩 근', 'x^(e-2)', 'x^(e-1)/(e-1)',
  { domain: D.pos,
  hints: ['$\\sqrt{x\\sqrt[3]{x\\sqrt[4]{x\\cdots}}}$ 의 지수를 세어 보라.',
          '$\\dfrac12+\\dfrac{1}{2\\cdot3}+\\dfrac{1}{2\\cdot3\\cdot4}+\\cdots=\\displaystyle\\sum_{n\\ge2}\\dfrac{1}{n!}=e-2$'],
  steps: ['지수의 합이 $\\sum_{n\\ge2}\\dfrac{1}{n!}=e-2$',
          '피적분함수는 $x^{e-2}$',
          '$=\\dfrac{x^{e-1}}{e-1}$'] });

add('medium', '항등식 정리', '1/(tan(x)+cot(x))', '-cos(2*x)/4',
  { domain: D.trig,
  hints: ['$\\tan x+\\cot x=\\dfrac{1}{\\sin x\\cos x}$ 다.',
          '역수는 $\\sin x\\cos x=\\dfrac{\\sin2x}{2}$'],
  steps: ['$\\tan x+\\cot x=\\dfrac{\\sin^{2}x+\\cos^{2}x}{\\sin x\\cos x}=\\dfrac{1}{\\sin x\\cos x}$',
          '$\\int\\dfrac{\\sin2x}{2}dx=-\\dfrac{\\cos2x}{4}$'] });

add('medium', '치환적분', 'x^5/(2+x^12)', 'atan(x^6/sqrt(2))/(6*sqrt(2))',
  { domain: D.poly,
  hints: ['$u=x^{6}$ 으로 두면 $du=6x^{5}dx$ 다.',
          '$x^{12}=u^{2}$'],
  steps: ['$u=x^{6}$ 치환 $\\Rightarrow\\dfrac16\\displaystyle\\int\\dfrac{du}{2+u^{2}}$',
          '$=\\dfrac{1}{6\\sqrt2}\\arctan\\dfrac{x^{6}}{\\sqrt2}$'] });

add('medium', '곱의 미분 되짚기', 'cos(x)*cosh(x)+sin(x)*sinh(x)', 'sin(x)*cosh(x)',
  { domain: [-1.2, 1.4],
  hints: ['$(\\sin x\\cosh x)\'$ 를 계산해 보라.',
          '$(\\cosh x)\'=\\sinh x$'],
  steps: ['$(\\sin x\\cosh x)\'=\\cos x\\cosh x+\\sin x\\sinh x$', '$=\\sin x\\cosh x$'] });

add('hard', '로그 미분', '(e^x+cos(x))/(e^x+sin(x))', 'ln(e^x+sin(x))',
  { domain: [0.2, 2.4], lnAbs: true,
  hints: ['분모의 도함수를 계산해 보라.',
          '$(e^{x}+\\sin x)\'=e^{x}+\\cos x$ — 분자와 같다.'],
  steps: ['$u=e^{x}+\\sin x$ 치환', '$=\\ln\\left|e^{x}+\\sin x\\right|$'] });

add('hard', '삼중 치환', 'sin(cos(sin(x)))*sin(sin(x))*cos(x)', 'cos(cos(sin(x)))',
  { domain: D.trigW,
  hints: ['$u=\\sin x$ 로 두면 $\\int\\sin(\\cos u)\\sin u\\,du$ 다.',
          '다시 $v=\\cos u$ 로 두면 $-\\int\\sin v\\,dv$ 다.'],
  steps: ['$u=\\sin x$, 그다음 $v=\\cos u$',
          '$-\\int\\sin v\\,dv=\\cos v$',
          '$=\\cos(\\cos(\\sin x))$'] });

add('medium', '유리화', '1/(1+sin(x))', 'tan(x)-1/cos(x)',
  { domain: D.trig,
  hints: ['분자·분모에 $1-\\sin x$ 를 곱한다.',
          '$\\dfrac{1-\\sin x}{\\cos^{2}x}=\\sec^{2}x-\\sec x\\tan x$'],
  steps: ['유리화한다', '$=\\tan x-\\sec x$'] });

add('medium', '배각 공식', 'cos(x)/(1-cos(2*x))', '-1/(2*sin(x))',
  { domain: [0.3, 1.5],
  hints: ['$1-\\cos2x=2\\sin^{2}x$ 다.',
          '$u=\\sin x$ 로 두면 $\\dfrac12\\displaystyle\\int u^{-2}du$ 다.'],
  steps: ['$\\dfrac{\\cos x}{2\\sin^{2}x}$ 로 고친다', '$=-\\dfrac{1}{2\\sin x}$'] });

add('medium', '미분 되짚기', 'e^x*(1/x+ln(x))', 'e^x*ln(x)',
  { domain: D.pos,
  hints: ['$\\int e^{x}(f+f\')dx=e^{x}f$ 꼴이다.',
          '$f=\\ln x$ 로 두면 $f\'=\\dfrac1x$ 다.'],
  steps: ['$f=\\ln x,\\ f\'=\\dfrac1x$', '$=e^{x}\\ln x$'] });

add('medium', '쌍곡선 항등식', 'tanh(x)^2', 'x-tanh(x)',
  { domain: D.hyp,
  hints: ['$\\tanh^{2}x=1-\\operatorname{sech}^{2}x$ 다.',
          '$\\int\\operatorname{sech}^{2}x\\,dx=\\tanh x$'],
  steps: ['$1-\\operatorname{sech}^{2}x$ 로 고친다', '$=x-\\tanh x$'] });

add('monster', '완전제곱 알아채기', '(2017*x^2016+2018*x^2017)/(1+x^4034+2*x^4035+x^4036)',
    'atan(x^2017+x^2018)',
  { domain: [0.998, 1.0005],
  hints: ['분모의 $x$ 항들을 완전제곱으로 묶어 보라.',
          '$x^{4034}+2x^{4035}+x^{4036}=\\left(x^{2017}+x^{2018}\\right)^{2}$'],
  steps: ['$y=x^{2017}+x^{2018}$ 로 두면 분모는 $1+y^{2}$',
          '$y\'=2017x^{2016}+2018x^{2017}$ — 분자와 같다',
          '$=\\arctan\\left(x^{2017}+x^{2018}\\right)$'] });

add('hard', '배각 공식', '(sin(2*x)-sin(x)^2)/(cos(2*x)-cos(x)^2)', 'x-2*ln(sin(x))',
  { domain: [0.3, 1.5], lnAbs: true,
  hints: ['$\\cos2x-\\cos^{2}x=\\cos^{2}x-1=-\\sin^{2}x$ 다.',
          '분자는 $\\sin x(2\\cos x-\\sin x)$ 로 묶인다.'],
  steps: ['분모 $=-\\sin^{2}x$',
          '$\\dfrac{\\sin x(2\\cos x-\\sin x)}{-\\sin^{2}x}=1-2\\cot x$',
          '$=x-2\\ln|\\sin x|$'] });

add('monster', '지수 정리', '1/(x^(25/25)*x^(16/25)+x^(9/25))', '(25/16)*atan(x^(16/25))',
  { domain: D.pos,
  hints: ['지수를 정리하면 $x^{41/25}+x^{9/25}=x^{9/25}\\left(x^{32/25}+1\\right)$ 이다.',
          '$u=x^{16/25}$ 로 두면 $du=\\dfrac{16}{25}x^{-9/25}dx$ 다.'],
  steps: ['$x^{9/25}$ 로 묶는다',
          '$u=x^{16/25}\\Rightarrow\\dfrac{25}{16}\\displaystyle\\int\\dfrac{du}{u^{2}+1}$',
          '$=\\dfrac{25}{16}\\arctan\\left(x^{16/25}\\right)$'] });

addDef('medium', '치환적분', 'cos(x)/(2-cos(x)^2)', 'pi/4',
  { lo: '0', hi: 'pi/2',
  hints: ['$2-\\cos^{2}x=1+\\sin^{2}x$ 다.',
          '$u=\\sin x$ 로 두면 $\\displaystyle\\int_{0}^{1}\\dfrac{du}{1+u^{2}}$ 다.'],
  steps: ['$1+\\sin^{2}x$ 로 고친다', '$=\\arctan1=\\dfrac{\\pi}{4}$'] });

add('medium', '삼각 치환', '1/(1+x^2)^(3/2)', 'x/sqrt(1+x^2)',
  { domain: D.all,
  hints: ['$x=\\tan\\theta$ 로 두면 $\\int\\cos\\theta\\,d\\theta$ 다.',
          '$\\sin\\theta=\\dfrac{x}{\\sqrt{1+x^{2}}}$'],
  steps: ['$x=\\tan\\theta$ 치환', '$=\\sin\\theta=\\dfrac{x}{\\sqrt{1+x^{2}}}$'] });

add('monster', '거듭제곱근 치환', '1/sqrt(x*sqrt(x)-x^2)', '4*asin(x^(1/4))',
  { domain: [0.05, 0.85],
  hints: ['$x\\sqrt x-x^{2}=x^{3/2}\\left(1-\\sqrt x\\right)$ 로 묶는다.',
          '$u=\\sqrt x$ 로 두면 $2\\displaystyle\\int\\dfrac{du}{\\sqrt{u(1-u)}}$ 다.'],
  steps: ['$u=\\sqrt x$ 치환',
          '$\\int\\dfrac{du}{\\sqrt{u(1-u)}}=2\\arcsin\\sqrt u$',
          '$=4\\arcsin\\left(x^{1/4}\\right)$'] });

add('monster', '로그 미분 되짚기', '(x-1)/(x+x^2*ln(x))', 'ln((1+x*ln(x))/x)',
  { domain: [0.4, 2.4], lnAbs: true,
  hints: ['분모를 $x(1+x\\ln x)$ 로 묶는다.',
          '$\\ln\\dfrac{1+x\\ln x}{x}$ 를 미분해 보라.'],
  steps: ['$\\left(\\ln\\dfrac{1+x\\ln x}{x}\\right)\'=\\dfrac{\\ln x+1}{1+x\\ln x}-\\dfrac1x$',
          '통분하면 $\\dfrac{x-1}{x(1+x\\ln x)}$',
          '$=\\ln\\left|\\dfrac{1+x\\ln x}{x}\\right|$'] });

add('medium', '배각 공식', 'csc(x)*sec(x)', 'ln(tan(x))',
  { domain: D.trig, lnAbs: true,
  hints: ['$\\csc x\\sec x=\\dfrac{1}{\\sin x\\cos x}$ 다.',
          '분자·분모를 $\\cos^{2}x$ 로 나누면 $\\dfrac{\\sec^{2}x}{\\tan x}$ 다.'],
  steps: ['$\\dfrac{\\sec^{2}x}{\\tan x}$ 로 고친다', '$=\\ln|\\tan x|$'] });

// --- 2019 -----------------------------------------------------------

addDef('hard', '대칭 논법', 'tan(cos(x))', '0',
  { lo: '0', hi: '2*pi',
  hints: ['$x\\to x+\\pi$ 를 넣으면 $\\cos$ 의 부호가 뒤집힌다.',
          '$\\tan$ 은 홀함수다.'],
  steps: ['$\\cos(x+\\pi)=-\\cos x$ 이므로 $f(x+\\pi)=-f(x)$',
          '한 주기 위에서 서로 상쇄된다',
          '$=0$'] });

add('hard', '로그 미분 되짚기', '(x+1)/(x*(x+ln(x)))', 'ln(x+ln(x))',
  { domain: [0.8, 3.0], lnAbs: true,
  hints: ['$(x+\\ln x)\'=1+\\dfrac1x=\\dfrac{x+1}{x}$ 다.',
          '분모의 도함수가 분자의 형태와 맞아떨어진다.'],
  steps: ['$u=x+\\ln x\\Rightarrow du=\\dfrac{x+1}{x}dx$',
          '$=\\ln\\left|x+\\ln x\\right|$'] });

add('hard', '이중 지수', 'e^(x+e^x)+e^(x-e^x)', 'e^(e^x)-e^(-e^x)',
  { domain: [-1.0, 1.2],
  hints: ['$e^{x}$ 를 묶어 내면 $e^{x}\\left(e^{e^{x}}+e^{-e^{x}}\\right)$ 다.',
          '$u=e^{x}$ 치환'],
  steps: ['$u=e^{x}\\Rightarrow\\int\\left(e^{u}+e^{-u}\\right)du$',
          '$=e^{u}-e^{-u}=e^{e^{x}}-e^{-e^{x}}$'] });

addDef('easy', '부분분수', '1/(1-x^2)', 'ln(3)',
  { lo: '-1/2', hi: '1/2',
  hints: ['$\\dfrac{1}{1-x^{2}}=\\dfrac12\\left(\\dfrac{1}{1-x}+\\dfrac{1}{1+x}\\right)$',
          '원시함수는 $\\dfrac12\\ln\\dfrac{1+x}{1-x}$ 다.'],
  steps: ['$\\left[\\dfrac12\\ln\\dfrac{1+x}{1-x}\\right]_{-1/2}^{1/2}$',
          '$=\\dfrac12\\ln3-\\dfrac12\\ln\\dfrac13=\\ln3$'] });

addDef('hard', '지수 정리', '2^ln(x)', '2^(ln(2)+1)/(ln(2)+1)',
  { lo: '0', hi: '2',
  hints: ['$2^{\\ln x}=e^{\\ln2\\cdot\\ln x}=x^{\\ln2}$ 다.',
          '거듭제곱 법칙을 쓰면 된다.'],
  steps: ['$2^{\\ln x}=x^{\\ln2}$',
          '$\\left[\\dfrac{x^{\\ln2+1}}{\\ln2+1}\\right]_{0}^{2}$',
          '$=\\dfrac{2^{\\ln2+1}}{\\ln2+1}$'] });

add('hard', '삼중 치환', 'cos(x)*cos(sin(x))*cos(sin(sin(x)))', 'sin(sin(sin(x)))',
  { domain: D.trigW,
  hints: ['$u=\\sin x$ 로 두면 $\\int\\cos u\\cos(\\sin u)du$ 다.',
          '다시 $v=\\sin u$ 로 두면 $\\int\\cos v\\,dv$ 다.'],
  steps: ['$u=\\sin x$, 그다음 $v=\\sin u$',
          '$=\\sin v=\\sin(\\sin(\\sin x))$'] });

addDef('hard', '역수 치환', 'e^(-2019/(4*x^2))/x^2', 'sqrt(pi/2019)',
  { lo: '0', hi: 'inf',
  hints: ['$u=\\dfrac1x$ 로 두면 $du=-\\dfrac{dx}{x^{2}}$ 다.',
          '$\\int_{0}^{\\infty}e^{-au^{2}}du=\\dfrac12\\sqrt{\\dfrac\\pi a}$'],
  steps: ['$u=\\dfrac1x\\Rightarrow\\displaystyle\\int_{0}^{\\infty}e^{-\\frac{2019}{4}u^{2}}du$',
          '$=\\dfrac12\\sqrt{\\dfrac{4\\pi}{2019}}=\\sqrt{\\dfrac{\\pi}{2019}}$'] });

addDef('medium', '거듭제곱근 치환', 'sqrt(x)/(1+x)', '2-pi/2',
  { lo: '0', hi: '1',
  hints: ['$u=\\sqrt x$ 로 두면 $2\\displaystyle\\int_{0}^{1}\\dfrac{u^{2}}{1+u^{2}}du$ 다.',
          '$\\dfrac{u^{2}}{1+u^{2}}=1-\\dfrac{1}{1+u^{2}}$'],
  steps: ['$u=\\sqrt x$ 치환',
          '$2\\left[u-\\arctan u\\right]_{0}^{1}$',
          '$=2\\left(1-\\dfrac{\\pi}{4}\\right)=2-\\dfrac{\\pi}{2}$'] });

addDef('hard', '곱-합 공식', 'cos(x)*cos(2*x)*cos(3*x)', 'pi/2',
  { lo: '0', hi: '2*pi',
  hints: ['$\\cos x\\cos2x=\\dfrac{\\cos3x+\\cos x}{2}$ 로 먼저 바꾼다.',
          '$\\cos^{2}3x$ 항만 살아남는다.'],
  steps: ['$\\dfrac{\\cos^{2}3x}{2}+\\dfrac{\\cos4x+\\cos2x}{4}$',
          '$\\int_{0}^{2\\pi}\\cos^{2}3x\\,dx=\\pi$, 나머지는 $0$',
          '$=\\dfrac{\\pi}{2}$'] });

addDef('hard', '합-곱 공식', '(sin(20*x)+sin(19*x))/(cos(20*x)+cos(19*x))',
    '-2*ln(cos(39*pi/200))/39',
  { lo: '0', hi: 'pi/100',
  hints: ['$\\sin A+\\sin B$ 와 $\\cos A+\\cos B$ 를 각각 곱으로 바꾼다.',
          '$\\cos\\dfrac{A-B}{2}$ 가 약분되어 $\\tan\\dfrac{A+B}{2}$ 만 남는다.'],
  steps: ['비가 $\\tan\\dfrac{39x}{2}$ 로 정리된다',
          '$\\left[-\\dfrac{2}{39}\\ln\\left|\\cos\\dfrac{39x}{2}\\right|\\right]_{0}^{\\pi/100}$',
          '$=-\\dfrac{2}{39}\\ln\\cos\\dfrac{39\\pi}{200}$'] });

add('hard', '곱의 미분 되짚기', 'e^x*cos(x)^2+e^x*sin(x)*cos(x)-e^x*sin(x)^2',
    'e^x*sin(x)*cos(x)',
  { domain: [-1.0, 1.5],
  hints: ['$f=\\sin x\\cos x$ 로 두고 $\\left(e^{x}f\\right)\'$ 를 계산해 보라.',
          '$f\'=\\cos^{2}x-\\sin^{2}x$'],
  steps: ['$\\left(e^{x}\\sin x\\cos x\\right)\'=e^{x}\\sin x\\cos x+e^{x}(\\cos^{2}x-\\sin^{2}x)$',
          '피적분함수와 같다'] });

addDef('monster', '킹 성질', 'sin(x)/sin(x+pi/4)', 'pi*sqrt(2)/4',
  { lo: '0', hi: 'pi/2',
  hints: ['$\\sin\\left(x+\\dfrac\\pi4\\right)=\\dfrac{\\sin x+\\cos x}{\\sqrt2}$ 다.',
          '$\\displaystyle\\int_{0}^{\\pi/2}\\dfrac{\\sin x}{\\sin x+\\cos x}dx=\\dfrac{\\pi}{4}$ 는 $x\\to\\dfrac\\pi2-x$ 로 얻는다.'],
  steps: ['$\\sqrt2\\displaystyle\\int_{0}^{\\pi/2}\\dfrac{\\sin x}{\\sin x+\\cos x}dx$',
          '$x\\to\\dfrac\\pi2-x$ 로 더하면 $2I=\\dfrac\\pi2$',
          '$=\\sqrt2\\cdot\\dfrac{\\pi}{4}$'] });

add('hard', '거듭제곱근 치환', '1/(x+x^(1/3))', '(3/2)*ln(x^(2/3)+1)',
  { domain: D.pos,
  hints: ['$u=x^{1/3}$ 로 두면 $dx=3u^{2}du$ 다.',
          '분모는 $u^{3}+u=u(u^{2}+1)$ 로 묶인다.'],
  steps: ['$u=x^{1/3}\\Rightarrow3\\displaystyle\\int\\dfrac{u\\,du}{u^{2}+1}$',
          '$=\\dfrac32\\ln\\left(x^{2/3}+1\\right)$'] });

addDef('monster', '지수 탑', 'x^(x^2+1)*(2*ln(x)+1)', '15',
  { lo: '0', hi: '2',
  hints: ['$x^{x^{2}}=e^{x^{2}\\ln x}$ 를 미분해 보라.',
          '$\\left(x^{x^{2}}\\right)\'=x^{x^{2}}\\left(2x\\ln x+x\\right)=x^{x^{2}+1}(2\\ln x+1)$'],
  steps: ['원시함수는 $x^{x^{2}}$',
          '$x\\to0^{+}$ 에서 $x^{x^{2}}\\to1$',
          '$=2^{4}-1=15$'] });

add('medium', '부분분수', '(2*x^3-1)/(x*(x^3+1))', '-ln(x)+ln(x^3+1)',
  { domain: [0.35, 2.6], lnAbs: true,
  hints: ['$\\dfrac{2x^{3}-1}{x(x^{3}+1)}+\\dfrac1x$ 를 통분해 보라.',
          '$=\\dfrac{3x^{2}}{x^{3}+1}$ 이 된다.'],
  steps: ['$-\\dfrac1x+\\dfrac{3x^{2}}{x^{3}+1}$ 로 쪼갠다',
          '$=-\\ln|x|+\\ln\\left|x^{3}+1\\right|$'] });

add('medium', '항등식 정리', 'cos(atan(x))', 'asinh(x)',
  { domain: D.all,
  hints: ['$\\cos(\\arctan x)=\\dfrac{1}{\\sqrt{1+x^{2}}}$ 다.',
          '$\\int\\dfrac{dx}{\\sqrt{1+x^{2}}}=\\operatorname{arsinh}x$'],
  steps: ['직각삼각형으로 $\\cos(\\arctan x)=\\dfrac{1}{\\sqrt{1+x^{2}}}$',
          '$=\\operatorname{arsinh}x$'] });


// --- 2020 -----------------------------------------------------------

add('hard', '로그 법칙', 'ln(2*x)/(x*ln(x))', 'ln(2)*ln(ln(x))+ln(x)',
  { domain: D.lnln, lnAbs: true,
  hints: ['$\\ln(2x)=\\ln2+\\ln x$ 로 쪼갠다.',
          '$\\dfrac{\\ln2}{x\\ln x}+\\dfrac1x$ 가 된다.'],
  steps: ['둘로 쪼갠다',
          '$\\int\\dfrac{dx}{x\\ln x}=\\ln|\\ln x|$',
          '$=\\ln2\\cdot\\ln|\\ln x|+\\ln|x|$'] });

addDef('medium', '지수 유리식', '1/(e^x+1)', 'ln(2)',
  { lo: '0', hi: 'inf',
  hints: ['$\\dfrac{1}{e^{x}+1}=1-\\dfrac{e^{x}}{e^{x}+1}$ 다.',
          '원시함수는 $x-\\ln(e^{x}+1)=\\ln\\dfrac{e^{x}}{e^{x}+1}$ 다.'],
  steps: ['$\\left[\\ln\\dfrac{e^{x}}{e^{x}+1}\\right]_{0}^{\\infty}$',
          '$=0-\\ln\\dfrac12=\\ln2$'] });

addDef('hard', '로그 치환', 'ln(x)*ln(ln(x))/x', '(e^2+1)/4',
  { lo: 'e', hi: 'e^e',
  hints: ['$u=\\ln x$ 로 두면 $\\displaystyle\\int_{1}^{e}u\\ln u\\,du$ 다.',
          '$\\int u\\ln u\\,du=\\dfrac{u^{2}\\ln u}{2}-\\dfrac{u^{2}}{4}$'],
  steps: ['$u=\\ln x$ 치환',
          '$\\left[\\dfrac{u^{2}\\ln u}{2}-\\dfrac{u^{2}}{4}\\right]_{1}^{e}$',
          '$=\\dfrac{e^{2}}{4}+\\dfrac14=\\dfrac{e^{2}+1}{4}$'] });

addDef('medium', '대칭 논법', 'ln((1+x)/(1-x))', '2*ln(2)',
  { lo: '0', hi: '1',
  hints: ['$\\ln(1+x)-\\ln(1-x)$ 로 쪼개 각각 적분한다.',
          '$\\int_{0}^{1}\\ln(1+x)dx=2\\ln2-1$, $\\int_{0}^{1}\\ln(1-x)dx=-1$'],
  steps: ['원시함수는 $(1+x)\\ln(1+x)+(1-x)\\ln(1-x)$',
          '$x\\to1^{-}$ 에서 $(1-x)\\ln(1-x)\\to0$',
          '$=2\\ln2$'] });

add('medium', '완전제곱', '1/(x^2+(x-1)^2)', 'atan(2*x-1)',
  { domain: D.all,
  hints: ['분모를 펼치면 $2x^{2}-2x+1$ 이다.',
          '$=\\dfrac{(2x-1)^{2}+1}{2}$'],
  steps: ['$2x^{2}-2x+1=\\dfrac{(2x-1)^{2}+1}{2}$',
          '$\\int\\dfrac{2\\,dx}{(2x-1)^{2}+1}=\\arctan(2x-1)$'] });

add('hard', '배각 공식', 'sin(x)^4*cos(x)^4*(cos(x)+sin(x))*(cos(x)-sin(x))',
    'sin(2*x)^5/160',
  { domain: D.trigW,
  hints: ['$(\\cos x+\\sin x)(\\cos x-\\sin x)=\\cos2x$ 다.',
          '$\\sin^{4}x\\cos^{4}x=\\dfrac{\\sin^{4}2x}{16}$'],
  steps: ['$\\dfrac{\\sin^{4}2x\\cos2x}{16}$ 로 정리',
          '$u=\\sin2x\\Rightarrow\\dfrac{1}{32}\\displaystyle\\int u^{4}du$',
          '$=\\dfrac{\\sin^{5}2x}{160}$'] });

add('medium', '부분적분', 'ln(1+x^2)', 'x*ln(1+x^2)-2*x+2*atan(x)',
  { domain: D.all,
  hints: ['$u=\\ln(1+x^{2}),\\ dv=dx$ 로 부분적분한다.',
          '남는 $\\displaystyle\\int\\dfrac{2x^{2}}{1+x^{2}}dx$ 는 나눗셈으로 푼다.'],
  steps: ['$x\\ln(1+x^{2})-\\displaystyle\\int\\dfrac{2x^{2}}{1+x^{2}}dx$',
          '$=x\\ln(1+x^{2})-2x+2\\arctan x$'] });

add('medium', '치환적분', '(2*x+1)/(2*x^2+2*x+1)', 'ln(2*x^2+2*x+1)/2',
  { domain: D.all,
  hints: ['분모의 도함수는 $4x+2$ 다.',
          '분자는 그 절반이다.'],
  steps: ['$u=2x^{2}+2x+1$ 치환', '$=\\dfrac{\\ln(2x^{2}+2x+1)}{2}$'] });

addDef('hard', '부분적분', 'asin(x)/x^3', '1/2',
  { lo: '1/sqrt(2)', hi: '1',
  hints: ['$u=\\arcsin x,\\ dv=x^{-3}dx$ 로 부분적분한다.',
          '$\\displaystyle\\int\\dfrac{dx}{x^{2}\\sqrt{1-x^{2}}}=-\\dfrac{\\sqrt{1-x^{2}}}{x}$'],
  steps: ['원시함수는 $-\\dfrac{\\arcsin x}{2x^{2}}-\\dfrac{\\sqrt{1-x^{2}}}{2x}$',
          '두 끝을 대입하면 $-\\dfrac{\\pi}{4}-\\left(-\\dfrac{\\pi}{4}-\\dfrac12\\right)$',
          '$=\\dfrac12$'] });

addDef('hard', '치환 후 부분적분', 'sin(2*x)*cos(cos(x))', '2*sin(1)+2*cos(1)-2',
  { lo: '0', hi: 'pi/2',
  hints: ['$\\sin2x=2\\sin x\\cos x$ 로 풀고 $u=\\cos x$ 로 둔다.',
          '$2\\displaystyle\\int_{0}^{1}u\\cos u\\,du$ 가 된다.'],
  steps: ['$u=\\cos x$ 치환',
          '$2\\left[u\\sin u+\\cos u\\right]_{0}^{1}$',
          '$=2\\sin1+2\\cos1-2$'] });

addDef('hard', '대칭 논법', 'sin(sin(x)-x)', '0',
  { lo: '0', hi: '2*pi',
  hints: ['$\\sin(\\sin x-x)=\\sin(\\sin x)\\cos x-\\cos(\\sin x)\\sin x$ 로 전개한다.',
          '두 항 모두 한 주기 위에서 사라진다.'],
  steps: ['$\\int_{0}^{2\\pi}\\sin(\\sin x)\\cos x\\,dx=\\left[-\\cos(\\sin x)\\right]_{0}^{2\\pi}=0$',
          '$\\cos(\\sin x)\\sin x$ 는 $x=\\pi$ 에 대해 홀함수라 $0$',
          '$=0$'] });

addDef('monster', '킹 성질', '1/(tan(x)^sqrt(2020)+1)', 'pi/4',
  { lo: '0', hi: 'pi/2',
  hints: ['$x\\to\\dfrac\\pi2-x$ 를 넣으면 $\\tan$ 이 $\\cot$ 으로 바뀐다.',
          '지수가 무엇이든 두 식을 더하면 $1$ 이다.'],
  steps: ['$f(x)+f\\left(\\dfrac\\pi2-x\\right)=1$', '$2I=\\dfrac\\pi2$', '$I=\\dfrac{\\pi}{4}$'] });

add('monster', '치환적분', 'x*(1-x)^2020', '(1-x)^2022/2022-(1-x)^2021/2021',
  { domain: [-0.0009, 0.0009],
  hints: ['$u=1-x$ 로 두면 $x=1-u$ 다.',
          '$\\int\\left(u^{2021}-u^{2020}\\right)du$ 만 남는다.'],
  steps: ['$u=1-x$ 치환',
          '$=\\dfrac{(1-x)^{2022}}{2022}-\\dfrac{(1-x)^{2021}}{2021}$'] });

add('hard', '치환적분', 'sec(x)^4*tan(x)/(sec(x)^4+4)', 'ln((1/cos(x))^4+4)/4',
  { domain: D.trig,
  hints: ['$u=\\sec^{4}x$ 로 두면 $du=4\\sec^{4}x\\tan x\\,dx$ 다.',
          '분자가 정확히 $\\dfrac{du}{4}$ 다.'],
  steps: ['$u=\\sec^{4}x$ 치환',
          '$\\dfrac14\\int\\dfrac{du}{u+4}=\\dfrac{\\ln(u+4)}{4}$'] });

add('hard', '지수 탑', 'x^(2*x)*(2+2*ln(x))', 'x^(2*x)',
  { domain: [0.45, 2.0],
  hints: ['$x^{2x}=e^{2x\\ln x}$ 로 쓰고 미분해 보라.',
          '$\\left(x^{2x}\\right)\'=x^{2x}(2\\ln x+2)$'],
  steps: ['$x^{2x}=e^{2x\\ln x}$',
          '지수의 도함수가 $2\\ln x+2$',
          '$=x^{2x}$'] });

addDef('monster', '감마 함수', 'x^5*e^(-x^4)', 'sqrt(pi)/8',
  { lo: '0', hi: 'inf',
  hints: ['$u=x^{4}$ 로 두면 $x^{5}dx=\\dfrac{u^{1/2}}{4}du$ 다.',
          '$\\Gamma\\left(\\dfrac32\\right)=\\dfrac{\\sqrt\\pi}{2}$'],
  steps: ['$u=x^{4}\\Rightarrow\\dfrac14\\displaystyle\\int_{0}^{\\infty}u^{1/2}e^{-u}du$',
          '$=\\dfrac14\\Gamma\\left(\\dfrac32\\right)=\\dfrac{\\sqrt\\pi}{8}$'] });

// --- 2022 -----------------------------------------------------------

add('medium', '로그 미분', '(1+cos(x))/(x+sin(x))', 'ln(x+sin(x))',
  { domain: [0.3, 2.6], lnAbs: true,
  hints: ['$(x+\\sin x)\'=1+\\cos x$ 다.', '분모의 도함수가 분자다.'],
  steps: ['$u=x+\\sin x$ 치환', '$=\\ln|x+\\sin x|$'] });

addDef('hard', '역삼각 항등식', '(atan(x)+acot(x))/x', 'pi*ln(3)/4',
  { lo: '1', hi: 'sqrt(3)',
  hints: ['$\\arctan x+\\operatorname{arccot}x=\\dfrac{\\pi}{2}$ 는 $x$ 와 무관한 상수다.',
          '남는 것은 $\\dfrac{\\pi}{2}\\displaystyle\\int_{1}^{\\sqrt3}\\dfrac{dx}{x}$ 다.'],
  steps: ['분자가 상수 $\\dfrac{\\pi}{2}$',
          '$\\dfrac{\\pi}{2}\\ln\\sqrt3=\\dfrac{\\pi\\ln3}{4}$'] });

add('medium', '쌍곡선 항등식', 'sinh(x)/(cosh(x)-sinh(x))', 'e^(2*x)/4-x/2',
  { domain: [-1.0, 1.5],
  hints: ['$\\cosh x-\\sinh x=e^{-x}$ 다.',
          '$e^{x}\\sinh x=\\dfrac{e^{2x}-1}{2}$'],
  steps: ['$\\dfrac{\\sinh x}{e^{-x}}=e^{x}\\sinh x=\\dfrac{e^{2x}-1}{2}$',
          '$=\\dfrac{e^{2x}}{4}-\\dfrac{x}{2}$'] });

add('hard', '유리화', 'x/(sqrt(x-1)+sqrt(x+1))',
    '(x+1)^(5/2)/5-(x+1)^(3/2)/3-(x-1)^(5/2)/5-(x-1)^(3/2)/3',
  { domain: [1.4, 3.4],
  hints: ['분모를 유리화하면 $\\dfrac{x\\left(\\sqrt{x+1}-\\sqrt{x-1}\\right)}{2}$ 다.',
          '$\\int x\\sqrt{x\\pm1}\\,dx$ 는 $u=x\\pm1$ 치환이다.'],
  steps: ['유리화한다',
          '$\\int x\\sqrt{x+1}dx=\\dfrac{2(x+1)^{5/2}}{5}-\\dfrac{2(x+1)^{3/2}}{3}$',
          '$\\int x\\sqrt{x-1}dx=\\dfrac{2(x-1)^{5/2}}{5}+\\dfrac{2(x-1)^{3/2}}{3}$'] });

add('medium', '치환 후 부분적분', 'x^3*sin(x^2)', '(sin(x^2)-x^2*cos(x^2))/2',
  { domain: D.poly,
  hints: ['$u=x^{2}$ 로 두면 $\\dfrac12\\displaystyle\\int u\\sin u\\,du$ 다.',
          '$\\int u\\sin u\\,du=\\sin u-u\\cos u$'],
  steps: ['$u=x^{2}$ 치환', '$=\\dfrac{\\sin(x^{2})-x^{2}\\cos(x^{2})}{2}$'] });

add('easy', '쌍곡선함수', '1/cosh(x)^2', 'tanh(x)',
  { domain: D.hyp,
  hints: ['$\\operatorname{sech}^{2}x$ 의 원시함수는 $\\tanh x$ 다.',
          '$(\\tanh x)\'=\\operatorname{sech}^{2}x$'],
  steps: ['$(\\tanh x)\'=\\dfrac{1}{\\cosh^{2}x}$', '$=\\tanh x$'] });

addDef('monster', '미분 되짚기', 'e^(e^x)-e^(e^x-x)', 'e^(e-1)-e',
  { lo: '0', hi: '1',
  hints: ['$e^{e^{x}}\\left(1-e^{-x}\\right)$ 로 묶는다.',
          '$\\left(e^{e^{x}-x}\\right)\'=e^{e^{x}-x}\\left(e^{x}-1\\right)$ 를 계산해 보라.'],
  steps: ['$\\left(e^{e^{x}-x}\\right)\'=e^{e^{x}}e^{-x}(e^{x}-1)=e^{e^{x}}\\left(1-e^{-x}\\right)$',
          '$\\left[e^{e^{x}-x}\\right]_{0}^{1}$',
          '$=e^{e-1}-e$'] });

addDef('medium', '거듭제곱근 치환', 'sqrt(1-sqrt(x))', '8/15',
  { lo: '0', hi: '1',
  hints: ['$u=\\sqrt x$ 로 두면 $2\\displaystyle\\int_{0}^{1}u\\sqrt{1-u}\\,du$ 다.',
          '다시 $w=1-u$ 로 두면 거듭제곱만 남는다.'],
  steps: ['$u=\\sqrt x$, 그다음 $w=1-u$',
          '$2\\displaystyle\\int_{0}^{1}\\left(w^{1/2}-w^{3/2}\\right)dw$',
          '$=2\\left(\\dfrac23-\\dfrac25\\right)=\\dfrac{8}{15}$'] });

add('monster', '로그 미분', 'x^3/(1+x+x^2/2+x^3/6)',
    '6*x-6*ln(x^3+3*x^2+6*x+6)',
  { domain: D.poly, lnAbs: true,
  hints: ['분모에 $6$ 을 곱해 $\\dfrac{6x^{3}}{x^{3}+3x^{2}+6x+6}$ 으로 만든다.',
          '$\\left(x^{3}+3x^{2}+6x+6\\right)\'=3x^{2}+6x+6$ 임을 눈여겨보라.'],
  steps: ['$6x^{3}=6\\left(x^{3}+3x^{2}+6x+6\\right)-6\\left(3x^{2}+6x+6\\right)$',
          '뒤 항은 분모의 도함수 꼴이다',
          '$=6x-6\\ln\\left|x^{3}+3x^{2}+6x+6\\right|$'] });

add('hard', '합-곱 공식', 'sin(x+sin(x))-sin(x-sin(x))', '-2*cos(sin(x))',
  { domain: D.trigW,
  hints: ['$\\sin A-\\sin B=2\\cos\\dfrac{A+B}{2}\\sin\\dfrac{A-B}{2}$',
          '$=2\\cos x\\sin(\\sin x)$ 가 된다.'],
  steps: ['합을 곱으로 바꾼다',
          '$u=\\sin x\\Rightarrow2\\displaystyle\\int\\sin u\\,du$',
          '$=-2\\cos(\\sin x)$'] });

add('monster', '곱의 미분 되짚기', 'tan(x)^4*sec(x)^3+tan(x)^2*sec(x)^5',
    'tan(x)^3/(3*cos(x)^3)',
  { domain: D.trig,
  hints: ['$\\left(\\tan^{3}x\\sec^{3}x\\right)\'$ 를 계산해 보라.',
          '$3\\tan^{2}x\\sec^{5}x+3\\tan^{4}x\\sec^{3}x$ 가 나온다.'],
  steps: ['$\\left(\\tan^{3}x\\sec^{3}x\\right)\'=3\\tan^{2}x\\sec^{5}x+3\\tan^{4}x\\sec^{3}x$',
          '피적분함수의 $3$ 배다',
          '$=\\dfrac{\\tan^{3}x\\sec^{3}x}{3}$'] });

add('monster', '부분적분', '(1+ln(x))*ln(ln(x))', 'x*ln(x)*ln(ln(x))-x',
  { domain: D.lnln,
  hints: ['$\\left(x\\ln x\\ln(\\ln x)\\right)\'$ 를 계산해 보라.',
          '$(x\\ln x)\'=1+\\ln x$ 이고 $\\left(\\ln(\\ln x)\\right)\'=\\dfrac{1}{x\\ln x}$ 다.'],
  steps: ['$\\left(x\\ln x\\ln(\\ln x)\\right)\'=(1+\\ln x)\\ln(\\ln x)+1$',
          '남는 $1$ 을 없애려면 $-x$ 를 더한다',
          '$=x\\ln x\\ln(\\ln x)-x$'] });

add('monster', '항등식 정리',
    '1/(1+sin(x))+1/(1+cos(x))+1/(1+tan(x))+1/(1+cot(x))+1/(1+sec(x))+1/(1+csc(x))',
    '3*x',
  { domain: D.trig,
  hints: ['$\\dfrac{1}{1+\\tan x}+\\dfrac{1}{1+\\cot x}=1$ 을 먼저 확인하라.',
          '$\\dfrac{1}{1+\\sec x}=\\dfrac{\\cos x}{1+\\cos x}$, $\\dfrac{1}{1+\\csc x}=\\dfrac{\\sin x}{1+\\sin x}$'],
  steps: ['$\\tan$ 짝은 합이 $1$',
          '나머지 넷은 $\\dfrac{1+\\sin x}{1+\\sin x}+\\dfrac{1+\\cos x}{1+\\cos x}=2$',
          '피적분함수는 상수 $3$ 이므로 $=3x$'] });

add('medium', '완전제곱', '1/sqrt(x-x^2)', 'asin(2*x-1)',
  { domain: [0.1, 0.9],
  hints: ['$x-x^{2}=\\dfrac14-\\left(x-\\dfrac12\\right)^{2}$ 로 완전제곱한다.',
          '$\\int\\dfrac{du}{\\sqrt{a^{2}-u^{2}}}=\\arcsin\\dfrac ua$'],
  steps: ['완전제곱 후 $u=x-\\dfrac12,\\ a=\\dfrac12$',
          '$=\\arcsin(2x-1)$'] });

addDef('easy', '거듭제곱 법칙', '1/(1-x)^4', '7/3',
  { lo: '0', hi: '1/2',
  hints: ['$u=1-x$ 로 두면 $\\int u^{-4}du$ 다.',
          '원시함수는 $\\dfrac{1}{3(1-x)^{3}}$ 이다.'],
  steps: ['$\\left[\\dfrac{1}{3(1-x)^{3}}\\right]_{0}^{1/2}$',
          '$=\\dfrac83-\\dfrac13=\\dfrac73$'] });

add('hard', '탄젠트 치환', '1/(1+cos(x)^2)', 'atan(tan(x)/sqrt(2))/sqrt(2)',
  { domain: D.trig,
  hints: ['분자·분모를 $\\cos^{2}x$ 로 나눈다.',
          '$\\dfrac{\\sec^{2}x}{\\tan^{2}x+2}$ 에서 $u=\\tan x$'],
  steps: ['$u=\\tan x$ 치환 $\\Rightarrow\\displaystyle\\int\\dfrac{du}{u^{2}+2}$',
          '$=\\dfrac{1}{\\sqrt2}\\arctan\\dfrac{\\tan x}{\\sqrt2}$'] });


// --- 2023 -----------------------------------------------------------

add('hard', '지수 정리', 'x^(1/ln(x))', 'e*x',
  { domain: D.lnln,
  hints: ['$x^{1/\\ln x}=e^{\\frac{\\ln x}{\\ln x}}$ 다.',
          '지수가 $1$ 로 딱 떨어져 피적분함수가 상수 $e$ 가 된다.'],
  steps: ['$x^{1/\\ln x}=e^{\\ln x\\cdot\\frac{1}{\\ln x}}=e$',
          '상수의 적분이므로 $=ex$'] });

add('hard', '이중 로그 치환', 'e^x/((1+e^x)*ln(1+e^x))', 'ln(ln(1+e^x))',
  { domain: D.all,
  hints: ['$u=\\ln(1+e^{x})$ 로 두면 $du=\\dfrac{e^{x}}{1+e^{x}}dx$ 다.',
          '$\\int\\dfrac{du}{u}=\\ln|u|$'],
  steps: ['$u=\\ln(1+e^{x})$ 치환', '$=\\ln\\left(\\ln(1+e^{x})\\right)$'] });

add('hard', '인수분해', '(1+x+x^2+x^3+x^4)*(1-x+x^2-x^3+x^4)',
    'x+x^3/3+x^5/5+x^7/7+x^9/9',
  { domain: D.poly,
  hints: ['$1+x+\\cdots+x^{4}=\\dfrac{x^{5}-1}{x-1}$, $1-x+\\cdots+x^{4}=\\dfrac{x^{5}+1}{x+1}$',
          '곱하면 $\\dfrac{x^{10}-1}{x^{2}-1}$ 이다.'],
  steps: ['$\\dfrac{x^{10}-1}{x^{2}-1}=1+x^{2}+x^{4}+x^{6}+x^{8}$',
          '항마다 거듭제곱 법칙을 쓴다'] });

addDef('hard', '대칭 논법', 'x*(x-1)*(x-2)*(x-3)*(x-4)/120', '0',
  { lo: '0', hi: '4',
  hints: ['구간의 한가운데는 $x=2$ 다.',
          '$t=x-2$ 로 옮기면 $\\dfrac{t(t^{2}-1)(t^{2}-4)}{120}$ 이 된다.'],
  steps: ['$t=x-2$ 로 평행이동',
          '$t\\left(t^{2}-1\\right)\\left(t^{2}-4\\right)$ 는 홀함수',
          '대칭 구간 $[-2,2]$ 에서 $=0$'] });

add('medium', '항별 적분', 'x+sin(x)+x*cos(x)+sin(x)*cos(x)',
    'x^2/2+x*sin(x)+sin(x)^2/2',
  { domain: D.trigW,
  hints: ['$\\int x\\cos x\\,dx=x\\sin x+\\cos x$ 는 부분적분이다.',
          '$\\cos x$ 가 $-\\cos x$ 와 상쇄된다.'],
  steps: ['$\\dfrac{x^{2}}{2}-\\cos x+(x\\sin x+\\cos x)+\\dfrac{\\sin^{2}x}{2}$',
          '$\\cos x$ 가 사라진다',
          '$=\\dfrac{x^{2}}{2}+x\\sin x+\\dfrac{\\sin^{2}x}{2}$'] });

add('hard', '항등식 정리',
    'sin(x)^2+cos(x)^2+tan(x)^2+cot(x)^2+sec(x)^2+csc(x)^2',
    '2*tan(x)-2*cot(x)-x',
  { domain: D.trig,
  hints: ['$\\tan^{2}x=\\sec^{2}x-1$, $\\cot^{2}x=\\csc^{2}x-1$ 로 바꾼다.',
          '$\\sin^{2}+\\cos^{2}=1$ 과 합치면 $2\\sec^{2}x+2\\csc^{2}x-1$ 이다.'],
  steps: ['$1+(\\sec^{2}-1)+(\\csc^{2}-1)+\\sec^{2}+\\csc^{2}=2\\sec^{2}x+2\\csc^{2}x-1$',
          '$=2\\tan x-2\\cot x-x$'] });

add('hard', '미분 되짚기', '(1+2*ln(x))*e^(ln(x)^2)', 'x*e^(ln(x)^2)',
  { domain: D.pos,
  hints: ['$\\left(xe^{(\\ln x)^{2}}\\right)\'$ 를 곱의 미분법으로 계산해 보라.',
          '$\\left(e^{(\\ln x)^{2}}\\right)\'=e^{(\\ln x)^{2}}\\cdot\\dfrac{2\\ln x}{x}$'],
  steps: ['$\\left(xe^{(\\ln x)^{2}}\\right)\'=e^{(\\ln x)^{2}}+2\\ln x\\,e^{(\\ln x)^{2}}$',
          '$=(1+2\\ln x)e^{(\\ln x)^{2}}$'] });

add('monster', '항등식 정리', 'sin(x)^6+cos(x)^6+3*sin(x)^2*cos(x)^2', 'x',
  { domain: D.trigW,
  hints: ['$a^{3}+b^{3}=(a+b)^{3}-3ab(a+b)$ 에 $a=\\sin^{2}x,\\ b=\\cos^{2}x$ 를 넣어 보라.',
          '$a+b=1$ 이므로 $\\sin^{6}+\\cos^{6}=1-3\\sin^{2}\\cos^{2}$ 다.'],
  steps: ['$\\sin^{6}x+\\cos^{6}x=1-3\\sin^{2}x\\cos^{2}x$',
          '더하면 피적분함수는 상수 $1$',
          '$=x$'] });

add('hard', '곱의 미분 되짚기', '(x+e+1)*x^e*e^x', 'x^(e+1)*e^x',
  { domain: D.pos,
  hints: ['$\\left(x^{e+1}e^{x}\\right)\'$ 를 계산해 보라.',
          '$(e+1)x^{e}e^{x}+x^{e+1}e^{x}=x^{e}e^{x}(e+1+x)$'],
  steps: ['$\\left(x^{e+1}e^{x}\\right)\'=x^{e}e^{x}(x+e+1)$',
          '$=x^{e+1}e^{x}$'] });

addDef('monster', '상쇄', 'x^2/(2-x^2)+sqrt(2*x/(x+1))', '1',
  { lo: '0', hi: '1',
  hints: ['두 조각을 따로 계산해 보라 — 로그 항이 서로 지워진다.',
          '앞은 $-1+\\dfrac{\\ln(3+2\\sqrt2)}{\\sqrt2}$, 뒤는 $2-\\dfrac{\\ln(3+2\\sqrt2)}{\\sqrt2}$ 다.'],
  steps: ['$\\displaystyle\\int_{0}^{1}\\dfrac{x^{2}}{2-x^{2}}dx=-1+\\dfrac{\\ln(3+2\\sqrt2)}{\\sqrt2}$',
          '$\\displaystyle\\int_{0}^{1}\\sqrt{\\dfrac{2x}{x+1}}dx=2-\\dfrac{\\ln(3+2\\sqrt2)}{\\sqrt2}$',
          '로그가 상쇄되어 $=1$'] });

add('monster', '부분분수', '(1+2*x^2022)/(x+x^2023)', 'ln(x)+ln(1+x^2022)/2022',
  { domain: [0.99, 1.003], lnAbs: true,
  hints: ['분모를 $x\\left(1+x^{2022}\\right)$ 로 묶는다.',
          '$\\dfrac{1+2x^{2022}}{x(1+x^{2022})}=\\dfrac1x+\\dfrac{x^{2021}}{1+x^{2022}}$'],
  steps: ['둘로 쪼갠다',
          '$=\\ln|x|+\\dfrac{\\ln\\left(1+x^{2022}\\right)}{2022}$'] });

add('hard', '곱-합 공식', '3*sin(20*x)*cos(23*x)+20*sin(43*x)',
    '(cos(3*x)-cos(43*x))/2',
  { domain: [0.05, 0.35],
  hints: ['$3\\sin20x\\cos23x=\\dfrac32\\left(\\sin43x-\\sin3x\\right)$',
          '$\\sin43x$ 항끼리 모으면 계수가 $\\dfrac{43}{2}$ 가 된다.'],
  steps: ['$\\dfrac{43}{2}\\sin43x-\\dfrac32\\sin3x$ 로 정리',
          '$=-\\dfrac{\\cos43x}{2}+\\dfrac{\\cos3x}{2}$'] });

add('monster', '로그 미분 되짚기', 'sin(x)/(2*e^x+cos(x)+sin(x))',
    'x/2-ln(2*e^x+cos(x)+sin(x))/2',
  { domain: [-0.5, 2.0], lnAbs: true,
  hints: ['분자·분모에 $e^{-x}$ 를 곱해 보라.',
          '$\\left(e^{-x}(\\cos x+\\sin x)\\right)\'=-2e^{-x}\\sin x$ 다.'],
  steps: ['$w=e^{-x}(\\cos x+\\sin x)$ 로 두면 $e^{-x}\\sin x\\,dx=-\\dfrac{dw}{2}$',
          '$-\\dfrac12\\displaystyle\\int\\dfrac{dw}{2+w}=-\\dfrac{\\ln|2+w|}{2}$',
          '$=\\dfrac x2-\\dfrac{\\ln\\left|2e^{x}+\\cos x+\\sin x\\right|}{2}$'] });

add('monster', '지수 정리', 'ln(x/pi)/ln(x)^ln(e*pi)', 'x/ln(x)^ln(pi)',
  { domain: D.lnln,
  hints: ['$\\ln(e\\pi)=1+\\ln\\pi$ 이고 $\\ln\\dfrac x\\pi=\\ln x-\\ln\\pi$ 다.',
          '$\\left(x(\\ln x)^{-\\ln\\pi}\\right)\'$ 를 계산해 보라.'],
  steps: ['피적분함수는 $(\\ln x)^{-\\ln\\pi}-\\ln\\pi\\,(\\ln x)^{-1-\\ln\\pi}$',
          '$\\left(x(\\ln x)^{-\\ln\\pi}\\right)\'$ 가 정확히 그 꼴이다',
          '$=\\dfrac{x}{(\\ln x)^{\\ln\\pi}}$'] });

addDef('hard', '평행이동', 'x^5+5*x^4+10*x^3+8*x^2+x', '5/6',
  { lo: '-3/2', hi: '-1/2',
  hints: ['$(x+1)^{5}$ 과 비교해 보라 — 차이가 간단하다.',
          '$x^{5}+5x^{4}+10x^{3}+8x^{2}+x=(x+1)^{5}-2(x+1)^{2}+1$'],
  steps: ['$t=x+1$ 로 옮기면 $\\displaystyle\\int_{-1/2}^{1/2}\\left(t^{5}-2t^{2}+1\\right)dt$',
          '$t^{5}$ 은 홀함수라 사라진다',
          '$=-\\dfrac16+1=\\dfrac56$'] });

// ================================================================== 검증 + 출력

var LEVELS = ['easy', 'medium', 'hard', 'monster'];
var LABELS = { easy: '쉬움', medium: '보통', hard: '어려움', monster: '몬스터' };
// medium 과 monster 가 같은 'm' 을 쓰지 않도록 접두어를 명시한다
var ID_PREFIX = { easy: 'e', medium: 'm', hard: 'h', monster: 'x' };

// 기준 부정적분을 수치 미분해 피적분함수와 맞는지 확인한다.
function checkOne(p) {
  var f, F;
  if (p.value !== undefined) return checkDefinite(p);
  try { f = M.compile(p.integrand); } catch (e) { return '피적분함수 파싱 실패: ' + e.message; }
  try { F = M.compile(p.answer); } catch (e) { return '기준답 파싱 실패: ' + e.message; }
  var lo = p.domain[0], hi = p.domain[1];
  var worst = 0, at = null, used = 0;
  for (var i = 1; i <= 14; i++) {
    var x = lo + (hi - lo) * i / 15;
    var target = f(x), got = M.derivative(F, x, 1e-5);
    if (!isFinite(target) || !isFinite(got)) continue;
    used++;
    var err = Math.abs(got - target) / Math.max(1, Math.abs(target));
    if (err > worst) { worst = err; at = x; }
  }
  if (used < 9) return '정의역에서 유효 표본이 ' + used + '개뿐';
  if (worst > 5e-5) return '불일치 rel.err=' + worst.toExponential(2) + ' (x=' + at.toFixed(3) + ')';
  if (!p.hints || p.hints.length < 2) return '힌트가 부족';
  if (!p.steps || p.steps.length < 1) return '풀이가 없음';
  return null;
}

// 정적분은 구적값과 기준값을 견준다.
function checkDefinite(p) {
  var f, v;
  try { f = M.compile(p.integrand); } catch (e) { return '피적분함수 파싱 실패: ' + e.message; }
  try { v = M.compile(p.value)(0); } catch (e) { return '기준값 파싱 실패: ' + e.message; }
  if (!isFinite(v)) return '기준값이 유한하지 않음';
  var got = M.integrate(f, limVal(p.lo), limVal(p.hi));
  if (!isFinite(got)) return '구적이 발산';
  var err = Math.abs(got - v) / Math.max(1, Math.abs(v));
  if (err > 1e-6) return '불일치 구적=' + got.toPrecision(10) + ' 기준=' + v.toPrecision(10) +
    ' (rel ' + err.toExponential(2) + ')';
  if (!p.hints || p.hints.length < 2) return '힌트가 부족';
  if (!p.steps || p.steps.length < 1) return '풀이가 없음';
  return null;
}

var failures = [];
out.forEach(function (p) {
  var why = checkOne(p);
  if (why) failures.push({ p: p, why: why });
});

if (failures.length) {
  console.error('검증 실패 ' + failures.length + '건 / 전체 ' + out.length + '건\n');
  failures.forEach(function (f) {
    console.error('  [' + f.p.level + '] ' + f.p.topic);
    console.error('    ∫ ' + f.p.integrand + ' dx');
    console.error('    F = ' + (f.p.answer !== undefined ? f.p.answer : '= ' + f.p.value));
    console.error('    구간 [' + (f.p.domain || (f.p.lo + ', ' + f.p.hi)) + ']  →  ' + f.why + '\n');
  });
  process.exit(1);
}

// 레벨별로 정렬하고 id 를 붙인다
var byLevel = {};
LEVELS.forEach(function (lv) {
  byLevel[lv] = out.filter(function (p) { return p.level === lv; });
  byLevel[lv].forEach(function (p, i) { p.id = ID_PREFIX[lv] + String(i + 1).padStart(3, '0'); });
});

function q(s) { return "'" + String(s).replace(/\\/g, '\\\\').replace(/'/g, "\\'") + "'"; }

function emit(p) {
  var head = '    {\n' +
    '      id: ' + q(p.id) + ', topic: ' + q(p.topic) + ',\n' +
    '      integrand: ' + q(p.integrand) + ', latex: ' + q(p.latex) + ',\n';
  var body = p.value !== undefined
    ? '      lo: ' + q(p.lo) + ', hi: ' + q(p.hi) + ',\n' +
      '      loLatex: ' + q(p.loLatex) + ', hiLatex: ' + q(p.hiLatex) + ',\n' +
      '      value: ' + q(p.value) + ', valueLatex: ' + q(p.valueLatex) + ',\n'
    : '      answer: ' + q(p.answer) + ', answerLatex: ' + q(p.answerLatex) + ',\n' +
      '      domain: [' + p.domain[0] + ', ' + p.domain[1] + '],\n';
  return head + body +
    '      hints: [' + p.hints.map(q).join(', ') + '],\n' +
    '      steps: [' + p.steps.map(q).join(', ') + ']\n' +
    '    }';
}

var body = LEVELS.map(function (lv) {
  return '  var ' + lv.toUpperCase() + ' = [\n' +
    byLevel[lv].map(emit).join(',\n') + '\n  ];';
}).join('\n\n');

var file = [
  '/*',
  ' * problems.js - 적분 문제 은행 (자동 생성 파일).',
  ' *',
  ' *   이 파일은 generate.js 가 만든다. 직접 고치지 말고 generate.js 를 고친 뒤',
  ' *   `node generate.js` 를 다시 실행할 것.',
  ' *',
  ' *   integrand : 채점·검증용 피적분함수(ASCII)',
  ' *   answer    : 기준 부정적분(ASCII, +C 생략)',
  ' *   domain    : 수치 비교에 쓰는 안전한 구간 (특이점 회피)',
  ' *',
  ' *   전체 ' + out.length + '문항 - ' +
    LEVELS.map(function (lv) { return LABELS[lv] + ' ' + byLevel[lv].length; }).join(' / '),
  ' */',
  '(function (root, factory) {',
  '  var api = factory();',
  '  root.PROBLEMS = api;',
  '  if (typeof module !== \'undefined\' && module.exports) module.exports = api;',
  '})(typeof globalThis !== \'undefined\' ? globalThis : this, function () {',
  '  \'use strict\';',
  '',
  body,
  '',
  '  var BY_LEVEL = { easy: EASY, medium: MEDIUM, hard: HARD, monster: MONSTER };',
  '  var ALL = [].concat(EASY, MEDIUM, HARD, MONSTER);',
  '',
  '  return {',
  '    easy: EASY, medium: MEDIUM, hard: HARD, monster: MONSTER,',
  '    all: ALL, byLevel: BY_LEVEL,',
  '    levels: [\'easy\', \'medium\', \'hard\', \'monster\'],',
  '    labels: { easy: \'쉬움\', medium: \'보통\', hard: \'어려움\', monster: \'몬스터\' },',
  '    find: function (id) {',
  '      for (var i = 0; i < ALL.length; i++) if (ALL[i].id === id) return ALL[i];',
  '      return null;',
  '    }',
  '  };',
  '});',
  ''
].join('\n');

fs.writeFileSync(__dirname + '/problems.js', file);

LEVELS.forEach(function (lv) { console.log(LABELS[lv] + ':', byLevel[lv].length); });
console.log('합계:', out.length, '— problems.js 를 다시 만들었습니다.');
