(() => {
  const $ = (id) => document.getElementById(id);
  const valueEl = $("value"), exprEl = $("expr"), moodEl = $("mood");
  const histEl = $("history"), sparkEl = $("sparkles"), keysEl = $("keys");
  const constellationEl = $("constellation");
  const graphCanvas = $("graphCanvas"), graphView = $("graphView");
  const distributionCanvas = $("distributionCanvas"), distributionView = $("distributionView");
  const scientificView = $("scientificView"), calcEl = document.querySelector(".calc");
  const settingsDialog = $("settingsDialog"), modeSelect = $("modeSelect");
  const stellarToggle = $("stellarToggle"), expressionList = $("expressionList");
  const distributionSelect = $("distributionSelect"), distributionParameters = $("distributionParameters");
  const distributionError = $("distributionError"), distributionMean = $("distributionMean");
  const distributionVariance = $("distributionVariance"), distributionHint = $("distributionHint");
  const addFunctionButton = $("addFunction");
  const degKey = $("degKey"), invKey = $("invKey");
  const flagAngle = $("flagAngle"), flagInv = $("flagInv");

  const MAX_LEN = 70;
  const MAX_GRAPH_FUNCTIONS = 8;
  const GRAPH_COLORS = ["#D8579C", "#5F7AC5", "#3E3A95", "#B23E82", "#7B8FC9", "#A44C82", "#5165A6", "#D98BB8"];
  const compliments = [
    "slay, queen *", "so smart omg <3", "math looks cute on you", "iconic answer +",
    "she's a genius!!", "totally nailed it *", "kyaa~ perfect <3", "level up! +"
  ];

  let s = { expr: "", done: false, line: "", result: 0, error: null, deg: true, inv: false };
  let ans = 0;
  const history = [];
  let graphFunctions = [{ id: 1, expression: "x^2", visible: true }];
  let nextGraphId = 2;
  let graphScale = 40, graphOffsetX = 0, graphOffsetY = 0;
  const distributionParams = {
    normal: { mean: 0, sd: 1 },
    binomial: { n: 10, p: .5 },
    poisson: { lambda: 4 },
  };

  /* ---------- number formatting ---------- */
  const clean = (n) => parseFloat(n.toPrecision(12));

  function group(str) {
    const neg = str.startsWith("-");
    const [i, d] = (neg ? str.slice(1) : str).split(".");
    const g = i.replace(/\B(?=(\d{3})+(?!\d))/g, ",");
    return (neg ? "-" : "") + g + (d !== undefined ? "." + d : "");
  }

  function fmt(n) {
    if (n === 0) return "0";
    const str = String(clean(n));
    if (/e/.test(str) || Math.abs(n) >= 1e12)
      return n.toExponential(6).replace(/\.?0+e/, "e").replace("e+", "e");
    return group(str);
  }

  /* ---------- evaluator ---------- */
  const NAMES = ["asin", "acos", "atan", "sqrt", "cbrt", "sin", "cos", "tan", "abs", "log", "ln", "Ans", "e"];
  const fail = (code) => { throw new Error(code); };

  function tokenize(str) {
    const out = [];
    let i = 0;
    while (i < str.length) {
      const rest = str.slice(i), c = str[i];
      let m;
      if (c === " ") { i++; continue; }
      if ((m = /^(\d+\.?\d*|\.\d+)/.exec(rest))) { out.push({ t: "num", v: parseFloat(m[1]) }); i += m[1].length; continue; }
      if (c === "π") { out.push({ t: "num", v: Math.PI }); i++; continue; }
      if (c === "x") { out.push({ t: "var", v: "x" }); i++; continue; }
      const name = NAMES.find((n) => rest.startsWith(n));
      if (name) {
        if (name === "e") out.push({ t: "num", v: Math.E });
        else if (name === "Ans") out.push({ t: "num", v: ans });
        else out.push({ t: "fn", v: name });
        i += name.length;
        continue;
      }
      if ("+-×÷*/^!%()".includes(c)) { out.push({ t: "op", v: c === "×" ? "*" : c === "÷" ? "/" : c }); i++; continue; }
      fail("syntax");
    }
    return out;
  }

  function evaluate(str, deg, x) {
    const open = (str.match(/\(/g) || []).length, close = (str.match(/\)/g) || []).length;
    const toks = tokenize(str + ")".repeat(Math.max(0, open - close)));
    let p = 0;
    const peek = () => toks[p];
    const isOp = (...vs) => peek() && peek().t === "op" && vs.includes(peek().v);
    const startsOperand = () => { const t = peek(); return t && (t.t === "num" || t.t === "var" || t.t === "fn" || (t.t === "op" && t.v === "(")); };

    const toRad = (x) => (deg ? (x * Math.PI) / 180 : x);
    const fromRad = (x) => (deg ? (x * 180) / Math.PI : x);
    const snap = (r) => (Math.abs(r) < 1e-12 ? 0 : r);

    const FN = {
      sin: (x) => snap(Math.sin(toRad(x))),
      cos: (x) => snap(Math.cos(toRad(x))),
      tan: (x) => {
        const c = Math.cos(toRad(x));
        if (Math.abs(c) < 1e-12) fail("domain");
        return snap(Math.tan(toRad(x)));
      },
      asin: (x) => (Math.abs(x) > 1 ? fail("domain") : fromRad(Math.asin(x))),
      acos: (x) => (Math.abs(x) > 1 ? fail("domain") : fromRad(Math.acos(x))),
      atan: (x) => fromRad(Math.atan(x)),
      ln: (x) => (x > 0 ? Math.log(x) : fail("domain")),
      log: (x) => (x > 0 ? Math.log10(x) : fail("domain")),
      sqrt: (x) => (x >= 0 ? Math.sqrt(x) : fail("domain")),
      cbrt: Math.cbrt,
      abs: Math.abs,
    };

    function fact(n) {
      if (n < 0 || n > 170 || Math.abs(n - Math.round(n)) > 1e-9) fail("domain");
      let r = 1;
      for (let i = 2; i <= Math.round(n); i++) r *= i;
      return r;
    }

    function expr() {
      let v = term();
      while (isOp("+", "-")) { const o = toks[p++].v; const r = term(); v = o === "+" ? v + r : v - r; }
      return v;
    }
    function term() {
      let v = unary();
      for (;;) {
        if (isOp("*", "/")) {
          const o = toks[p++].v, r = unary();
          if (o === "/" && r === 0) fail("div0");
          v = o === "*" ? v * r : v / r;
        } else if (startsOperand()) v *= unary(); // implicit multiplication: 2π, 3(4)
        else break;
      }
      return v;
    }
    function unary() {
      if (isOp("-")) { p++; return -unary(); }
      if (isOp("+")) { p++; return unary(); }
      return power();
    }
    function power() {
      const base = postfix();
      if (isOp("^")) { p++; const r = Math.pow(base, unary()); return Number.isNaN(r) ? fail("domain") : r; }
      return base;
    }
    function postfix() {
      let v = primary();
      while (isOp("!", "%")) v = toks[p++].v === "!" ? fact(v) : v / 100;
      return v;
    }
    function primary() {
      const t = toks[p++];
      if (!t) fail("syntax");
      if (t.t === "num") return t.v;
      if (t.t === "var") {
        if (typeof x !== "number") fail("syntax");
        return x;
      }
      if (t.t === "op" && t.v === "(") {
        const v = expr();
        if (!isOp(")")) fail("syntax");
        p++;
        return v;
      }
      if (t.t === "fn") {
        if (!isOp("(")) fail("syntax");
        p++;
        const v = expr();
        if (!isOp(")")) fail("syntax");
        p++;
        return FN[t.v](v);
      }
      return fail("syntax");
    }

    const r = expr();
    if (p < toks.length) fail("syntax");
    if (!Number.isFinite(r)) fail("domain");
    return r;
  }

  /* ---------- render ---------- */
  function say(msg) { moodEl.textContent = msg; }

  function render() {
    let text = "0", cls = "value";
    if (s.error) {
      text = s.error === "div0" ? "can't divide by 0, bestie" : s.error === "domain" ? "that's not real, babe" : "check your brackets <3";
      cls += " error";
      exprEl.textContent = "\u00a0";
    } else if (s.done) {
      text = fmt(s.result);
      exprEl.textContent = s.line + " =";
    } else {
      exprEl.textContent = s.expr || "\u00a0";
      if (s.expr) {
        try { text = fmt(evaluate(s.expr, s.deg)); } catch { text = "..."; }
      }
    }
    if (!s.error) cls += text.length > 12 ? " tiny" : text.length > 8 ? " small" : "";
    valueEl.textContent = text;
    valueEl.className = cls;

    flagAngle.textContent = s.deg ? "DEG" : "RAD";
    flagInv.hidden = !s.inv;
    degKey.textContent = s.deg ? "DEG" : "RAD";
    invKey.classList.toggle("on", s.inv);
    invKey.setAttribute("aria-pressed", String(s.inv));
    keysEl.querySelectorAll("[data-inv-ins]").forEach((b) => {
      b.textContent = s.inv ? b.dataset.invLbl : b.dataset.lbl;
    });
  }

  /* ---------- input ---------- */
  const isBinary = (c) => "+-×÷^".includes(c);

  function insert(text, kind) {
    if (s.error) s = { ...s, expr: "", done: false, error: null };
    if (s.done) {
      s.expr = kind === "op" || kind === "post" ? "Ans" : "";
      s.done = false;
    }
    if (s.inv && s.expr !== undefined && keysEl.querySelector(`[data-inv-ins="${text}"]`)) s.inv = false;

    let e = s.expr;
    const last = e.slice(-1);

    if (kind === "op" && !e) e = "Ans";
    if (kind === "post" && !e) e = "Ans";
    if (kind === "op") {
      const ins = text;
      if (text === "-" && last !== "-" && last !== "+") e += ins;
      else if (isBinary(e.slice(-1)) && e.length > 0) e = e.slice(0, -1) + ins;
      else e += ins;
    } else if (kind === "num") {
      if (/(Ans|e|π|\)|!|%)$/.test(e)) e += "×";
      e += text;
    } else if (kind === "const" || kind === "fn" || kind === "open") {
      if (/(\d|Ans|e|π|\)|!|%)$/.test(e) && kind !== "open") e += "×";
      e += text;
    } else {
      e += text;
    }
    if (e.length <= MAX_LEN) s.expr = e;
    render();
  }

  function decimal() {
    if (s.error || s.done) { s = { ...s, expr: "", done: false, error: null }; }
    const seg = /[\d.]*$/.exec(s.expr)[0];
    if (seg.includes(".")) return;
    s.expr += seg === "" ? "0." : ".";
    render();
  }

  function back() {
    if (s.error || s.done) { s = { ...s, expr: "", done: false, error: null }; say("fresh start, babe *"); render(); return; }
    s.expr = s.expr.replace(/(asin\(|acos\(|atan\(|sqrt\(|cbrt\(|sin\(|cos\(|tan\(|abs\(|log\(|ln\(|Ans|.)$/, "");
    render();
  }

  function recip() {
    if (s.error) s = { ...s, expr: "", done: false, error: null };
    const inner = s.done || !s.expr ? "Ans" : s.expr;
    s.expr = `1÷(${inner})`;
    s.done = false;
    render();
  }

  function equals() {
    if (s.error || s.done || !s.expr) return;
    try {
      const r = clean(evaluate(s.expr, s.deg));
      history.unshift([s.expr, fmt(r)]);
      if (history.length > 6) history.pop();
      histEl.innerHTML = history.map(([l, v]) => `<li><span>${l.replace(/</g, "&lt;")}</span><b>${v}</b></li>`).join("");
      ans = r;
      s = { ...s, line: s.expr, result: r, done: true };
      say(compliments[Math.floor(Math.random() * compliments.length)]);
      render();
      burst();
    } catch (err) {
      s.error = ["div0", "domain"].includes(err.message) ? err.message : "syntax";
      say("oops! try again <3");
      render();
    }
  }

  function clearAll() { s = { ...s, expr: "", done: false, error: null, inv: false }; say("fresh start, babe *"); render(); }

  /* ---------- sparkles ---------- */
  function burst() {
    if (matchMedia("(prefers-reduced-motion: reduce)").matches) return;
    const box = valueEl.getBoundingClientRect();
    const colours = ["#D8579C", "#EEBCDC", "#5F7AC5", "#FFFBFD"];
    for (let i = 0; i < 14; i++) {
      const el = document.createElement("i");
      const a = Math.random() * Math.PI * 2, d = 50 + Math.random() * 100;
      el.style.cssText =
        `left:${box.left + box.width / 2}px;top:${box.top + box.height / 2}px;` +
        `--x:${Math.round(Math.cos(a) * d)}px;--y:${Math.round(Math.sin(a) * d)}px;--c:${colours[i % 4]}`;
      sparkEl.appendChild(el);
      el.addEventListener("animationend", () => el.remove());
    }
  }

  /* ---------- constellation field ---------- */
  function initConstellation() {
    const ctx = constellationEl.getContext("2d");
    if (!ctx) return { setEnabled: (enabled) => { constellationEl.hidden = !enabled; } };

    const colors = ["#D8579C", "#EEBCDC", "#5F7AC5"];
    const linkDistance = 120;
    const reduceMotion = matchMedia("(prefers-reduced-motion: reduce)").matches;
    let width = 0, height = 0, points = [], frame = null, startTime = null;
    let enabled = true;

    function resize() {
      const ratio = Math.min(window.devicePixelRatio || 1, 2);
      width = window.innerWidth;
      height = window.innerHeight;
      constellationEl.width = Math.round(width * ratio);
      constellationEl.height = Math.round(height * ratio);
      ctx.setTransform(ratio, 0, 0, ratio, 0, 0);

      const count = Math.min(46, Math.floor((width * height) / 14000));
      points = Array.from({ length: count }, () => ({
        x: Math.random() * width,
        y: Math.random() * height,
        vx: (Math.random() - .5) * .15,
        vy: (Math.random() - .5) * .15,
        radius: Math.random() * 1.6 + .6,
        color: colors[Math.floor(Math.random() * colors.length)],
        phase: Math.random() * Math.PI * 2,
        flickers: Math.random() < .6,
        frequency: .8 * (.7 + Math.random() * .6),
      }));

      if (reduceMotion) draw(0);
    }

    function draw(timestamp) {
      frame = null;
      if (startTime === null) startTime = timestamp;
      const elapsed = (timestamp - startTime) / 1000;
      ctx.clearRect(0, 0, width, height);

      if (!reduceMotion) {
        points.forEach((point) => {
          point.x += point.vx;
          point.y += point.vy;
          if (point.x < 0 || point.x > width) point.vx *= -1;
          if (point.y < 0 || point.y > height) point.vy *= -1;
        });
      }

      for (let i = 0; i < points.length; i++) {
        for (let j = i + 1; j < points.length; j++) {
          const a = points[i], b = points[j];
          const distance = Math.hypot(a.x - b.x, a.y - b.y);
          if (distance < linkDistance) {
            ctx.strokeStyle = `rgba(216, 87, 156, ${.3 * (1 - distance / linkDistance)})`;
            ctx.lineWidth = 1;
            ctx.beginPath();
            ctx.moveTo(a.x, a.y);
            ctx.lineTo(b.x, b.y);
            ctx.stroke();
          }
        }
      }

      points.forEach((point) => {
        const pulse = (Math.sin(elapsed * point.frequency * Math.PI * 2 + point.phase) + 1) / 2;
        ctx.globalAlpha = !reduceMotion && point.flickers ? .8 * (.4 + .6 * pulse) : .8;
        ctx.beginPath();
        ctx.arc(point.x, point.y, point.radius, 0, Math.PI * 2);
        ctx.fillStyle = point.color;
        ctx.fill();
      });
      ctx.globalAlpha = 1;

      if (enabled && !reduceMotion && !document.hidden) frame = requestAnimationFrame(draw);
    }

    function stop() {
      if (frame !== null) cancelAnimationFrame(frame);
      frame = null;
    }

    function start() {
      if (enabled && !reduceMotion && !document.hidden && frame === null)
        frame = requestAnimationFrame(draw);
    }

    function handleVisibility() {
      if (document.hidden) stop();
      else {
        startTime = null;
        start();
      }
    }

    resize();
    start();
    window.addEventListener("resize", resize);
    document.addEventListener("visibilitychange", handleVisibility);

    return {
      setEnabled(value) {
        enabled = value;
        constellationEl.hidden = !enabled;
        if (enabled && reduceMotion) draw(0);
        else if (enabled) {
          startTime = null;
          start();
        }
        else stop();
      },
    };
  }

  /* ---------- graphing mode ---------- */
  const graphCtx = graphCanvas.getContext("2d");
  let graphDrag = null;

  function drawGraph() {
    if (!graphCtx || graphView.hidden) return;

    const rect = graphCanvas.getBoundingClientRect();
    const width = rect.width, height = rect.height;
    if (!width || !height) return;

    const ratio = Math.min(window.devicePixelRatio || 1, 2);
    graphCanvas.width = Math.round(width * ratio);
    graphCanvas.height = Math.round(height * ratio);
    graphCtx.setTransform(ratio, 0, 0, ratio, 0, 0);
    graphCtx.fillStyle = "#FFFBFD";
    graphCtx.fillRect(0, 0, width, height);

    const zeroX = width / 2 + graphOffsetX;
    const zeroY = height / 2 + graphOffsetY;
    const rawStep = 50 / graphScale;
    const magnitude = Math.pow(10, Math.floor(Math.log10(rawStep)));
    const normalized = rawStep / magnitude;
    const gridStep = (normalized < 1.5 ? 1 : normalized < 3.5 ? 2 : normalized < 7.5 ? 5 : 10) * magnitude;
    const formatTick = (value) => Number(value.toPrecision(3)).toString();

    graphCtx.strokeStyle = "rgba(95, 122, 197, .15)";
    graphCtx.lineWidth = 1;
    graphCtx.beginPath();
    const firstX = Math.floor(-zeroX / (gridStep * graphScale));
    const lastX = Math.ceil((width - zeroX) / (gridStep * graphScale));
    for (let i = firstX; i <= lastX; i++) {
      const px = zeroX + i * gridStep * graphScale;
      graphCtx.moveTo(px, 0);
      graphCtx.lineTo(px, height);
    }
    const firstY = Math.floor(-(height - zeroY) / (gridStep * graphScale));
    const lastY = Math.ceil(zeroY / (gridStep * graphScale));
    for (let i = firstY; i <= lastY; i++) {
      const py = zeroY - i * gridStep * graphScale;
      graphCtx.moveTo(0, py);
      graphCtx.lineTo(width, py);
    }
    graphCtx.stroke();

    graphCtx.strokeStyle = "rgba(34, 29, 46, .55)";
    graphCtx.lineWidth = 1.5;
    graphCtx.beginPath();
    graphCtx.moveTo(zeroX, 0);
    graphCtx.lineTo(zeroX, height);
    graphCtx.moveTo(0, zeroY);
    graphCtx.lineTo(width, zeroY);
    graphCtx.stroke();

    graphCtx.fillStyle = "#5B5468";
    graphCtx.font = '12px "Karla", sans-serif';
    graphCtx.textBaseline = "top";
    for (let i = firstX; i <= lastX; i++) {
      if (i === 0) continue;
      const px = zeroX + i * gridStep * graphScale;
      if (px > 0 && px < width - 18 && zeroY > 0 && zeroY < height - 18)
        graphCtx.fillText(formatTick(i * gridStep), px + 3, zeroY + 4);
    }
    graphCtx.textBaseline = "alphabetic";
    for (let i = firstY; i <= lastY; i++) {
      if (i === 0) continue;
      const py = zeroY - i * gridStep * graphScale;
      if (py > 13 && py < height && zeroX > 2 && zeroX < width - 28)
        graphCtx.fillText(formatTick(i * gridStep), zeroX + 5, py - 3);
    }

    graphFunctions.forEach((fn, index) => {
      if (!fn.visible || !fn.expression.trim()) return;
      graphCtx.strokeStyle = GRAPH_COLORS[index % GRAPH_COLORS.length];
      graphCtx.lineWidth = 2.5;
      graphCtx.lineJoin = "round";
      graphCtx.lineCap = "round";
      graphCtx.beginPath();
      let active = false, previousY = 0;

      for (let px = 0; px <= width; px += 2) {
        const x = (px - zeroX) / graphScale;
        let y;
        try {
          y = evaluate(fn.expression, false, x);
        } catch {
          active = false;
          continue;
        }

        const py = zeroY - y * graphScale;
        if (!Number.isFinite(py) || py < -height * 3 || py > height * 4) {
          active = false;
          continue;
        }
        if (!active || Math.abs(py - previousY) > height * 1.25) graphCtx.moveTo(px, py);
        else graphCtx.lineTo(px, py);
        active = true;
        previousY = py;
      }
      graphCtx.stroke();
    });
  }

  function renderGraphFunctions(focusId) {
    expressionList.replaceChildren();
    graphFunctions.forEach((fn, index) => {
      const row = document.createElement("div");
      row.className = "expression-row";
      row.style.setProperty("--graph-color", GRAPH_COLORS[index % GRAPH_COLORS.length]);

      const visible = document.createElement("input");
      visible.type = "checkbox";
      visible.checked = fn.visible;
      visible.setAttribute("aria-label", `Show function ${index + 1}`);
      visible.addEventListener("change", () => {
        fn.visible = visible.checked;
        drawGraph();
      });

      const prefix = document.createElement("span");
      prefix.className = "equation-prefix";
      prefix.textContent = "y =";

      const input = document.createElement("input");
      input.type = "text";
      input.value = fn.expression;
      input.maxLength = MAX_LEN;
      input.autocomplete = "off";
      input.spellcheck = false;
      input.placeholder = "e.g. sin(x)";
      input.setAttribute("aria-label", `Function ${index + 1}`);
      input.addEventListener("input", () => {
        fn.expression = input.value;
        drawGraph();
      });

      const remove = document.createElement("button");
      remove.type = "button";
      remove.className = "remove-function";
      remove.textContent = "×";
      remove.disabled = graphFunctions.length === 1;
      remove.setAttribute("aria-label", `Remove function ${index + 1}`);
      remove.addEventListener("click", () => {
        graphFunctions = graphFunctions.filter((item) => item.id !== fn.id);
        renderGraphFunctions();
        drawGraph();
      });

      row.append(visible, prefix, input, remove);
      expressionList.append(row);
      if (fn.id === focusId) input.focus();
    });
    addFunctionButton.disabled = graphFunctions.length >= MAX_GRAPH_FUNCTIONS;
    addFunctionButton.textContent = graphFunctions.length >= MAX_GRAPH_FUNCTIONS ? "Function limit reached" : "+ Add function";
  }

  /* ---------- probability distributions ---------- */
  const distributionCtx = distributionCanvas.getContext("2d");

  function renderDistributionControls() {
    const type = distributionSelect.value;
    const fields = {
      normal: [
        { key: "mean", label: "Mean (μ)", min: -100, max: 100, step: .1 },
        { key: "sd", label: "Std. deviation (σ)", min: .01, max: 20, step: .01 },
      ],
      binomial: [
        { key: "n", label: "Trials (n)", min: 1, max: 100, step: 1 },
        { key: "p", label: "Success probability (p)", min: 0, max: 1, step: .01 },
      ],
      poisson: [
        { key: "lambda", label: "Rate (λ)", min: 0, max: 50, step: .1 },
      ],
    }[type];

    distributionParameters.replaceChildren();
    fields.forEach((field) => {
      const label = document.createElement("label");
      label.className = "setting-field distribution-field";
      label.append(document.createElement("span"));
      label.lastChild.textContent = field.label;

      const input = document.createElement("input");
      input.type = "number";
      input.min = String(field.min);
      input.max = String(field.max);
      input.step = String(field.step);
      input.value = String(distributionParams[type][field.key]);
      input.setAttribute("aria-label", field.label);
      input.addEventListener("input", () => {
        distributionParams[type][field.key] = input.value === "" ? NaN : Number(input.value);
        drawDistribution();
      });

      label.append(input);
      distributionParameters.append(label);
    });
    drawDistribution();
  }

  function binomialProbability(n, k, p) {
    if (p === 0) return k === 0 ? 1 : 0;
    if (p === 1) return k === n ? 1 : 0;
    let logCoefficient = 0;
    for (let i = 1; i <= k; i++) logCoefficient += Math.log(n - i + 1) - Math.log(i);
    return Math.exp(logCoefficient + k * Math.log(p) + (n - k) * Math.log1p(-p));
  }

  function niceTick(raw) {
    const magnitude = Math.pow(10, Math.floor(Math.log10(raw)));
    const normalized = raw / magnitude;
    return (normalized <= 1 ? 1 : normalized <= 2 ? 2 : normalized <= 5 ? 5 : 10) * magnitude;
  }

  function drawDistribution() {
    if (!distributionCtx || distributionView.hidden) return;
    const rect = distributionCanvas.getBoundingClientRect();
    const width = rect.width, height = rect.height;
    if (!width || !height) return;

    const ratio = Math.min(window.devicePixelRatio || 1, 2);
    distributionCanvas.width = Math.round(width * ratio);
    distributionCanvas.height = Math.round(height * ratio);
    distributionCtx.setTransform(ratio, 0, 0, ratio, 0, 0);
    distributionCtx.fillStyle = "#FFFBFD";
    distributionCtx.fillRect(0, 0, width, height);

    const type = distributionSelect.value;
    const params = distributionParams[type];
    let error = "";
    if (type === "normal" && (!Number.isFinite(params.mean) || !Number.isFinite(params.sd) || params.sd <= 0 || params.sd > 20))
      error = "Enter a finite mean and a standard deviation from 0.01 to 20.";
    if (type === "binomial" && (!Number.isInteger(params.n) || params.n < 1 || params.n > 100 || !Number.isFinite(params.p) || params.p < 0 || params.p > 1))
      error = "Use 1–100 whole-number trials and a probability from 0 to 1.";
    if (type === "poisson" && (!Number.isFinite(params.lambda) || params.lambda < 0 || params.lambda > 50))
      error = "Enter a rate from 0 to 50.";
    distributionError.textContent = error;
    distributionError.hidden = !error;
    if (error) {
      distributionMean.textContent = "—";
      distributionVariance.textContent = "—";
      return;
    }

    let points, minX, maxX, maxY, expected, variance, isDiscrete;
    if (type === "normal") {
      const { mean, sd } = params;
      minX = mean - 4 * sd;
      maxX = mean + 4 * sd;
      expected = mean;
      variance = sd * sd;
      isDiscrete = false;
      points = Array.from({ length: 241 }, (_, i) => {
        const x = minX + (maxX - minX) * i / 240;
        const z = (x - mean) / sd;
        return { x, y: Math.exp(-.5 * z * z) / (sd * Math.sqrt(2 * Math.PI)) };
      });
    } else if (type === "binomial") {
      const { n, p } = params;
      expected = n * p;
      variance = n * p * (1 - p);
      isDiscrete = true;
      points = Array.from({ length: n + 1 }, (_, k) => ({ x: k, y: binomialProbability(n, k, p) }));
      minX = -.5;
      maxX = n + .5;
    } else {
      const { lambda } = params;
      expected = lambda;
      variance = lambda;
      isDiscrete = true;
      const end = Math.min(100, Math.ceil(lambda + 4 * Math.sqrt(lambda) + 8));
      let probability = Math.exp(-lambda);
      points = Array.from({ length: end + 1 }, (_, k) => {
        if (k > 0) probability *= lambda / k;
        return { x: k, y: probability };
      });
      minX = -.5;
      maxX = end + .5;
    }

    maxY = Math.max(...points.map((point) => point.y)) * 1.12;
    distributionMean.textContent = Number(expected.toPrecision(4)).toString();
    distributionVariance.textContent = Number(variance.toPrecision(4)).toString();
    const padding = { left: 54, right: 18, top: 20, bottom: 42 };
    const plotWidth = width - padding.left - padding.right;
    const plotHeight = height - padding.top - padding.bottom;
    const xPosition = (x) => padding.left + (x - minX) / (maxX - minX) * plotWidth;
    const yPosition = (y) => padding.top + plotHeight - y / maxY * plotHeight;
    const yStep = niceTick(maxY / 4);
    const formatTick = (value) => Number(value.toPrecision(3)).toString();

    distributionCtx.font = '12px "Karla", sans-serif';
    distributionCtx.textBaseline = "middle";
    distributionCtx.textAlign = "right";
    distributionCtx.strokeStyle = "rgba(95, 122, 197, .15)";
    distributionCtx.lineWidth = 1;
    distributionCtx.beginPath();
    for (let value = 0; value <= maxY + yStep * .01; value += yStep) {
      const y = yPosition(value);
      distributionCtx.moveTo(padding.left, y);
      distributionCtx.lineTo(width - padding.right, y);
      distributionCtx.fillStyle = "#5B5468";
      distributionCtx.fillText(formatTick(value), padding.left - 8, y);
    }
    distributionCtx.stroke();

    distributionCtx.strokeStyle = "rgba(34, 29, 46, .55)";
    distributionCtx.lineWidth = 1.5;
    distributionCtx.beginPath();
    distributionCtx.moveTo(padding.left, padding.top);
    distributionCtx.lineTo(padding.left, padding.top + plotHeight);
    distributionCtx.lineTo(width - padding.right, padding.top + plotHeight);
    distributionCtx.stroke();

    const xTicks = isDiscrete
      ? points.filter((point, index) => index % Math.max(1, Math.ceil(points.length / 12)) === 0 || index === points.length - 1).map((point) => point.x)
      : Array.from({ length: 5 }, (_, i) => minX + (maxX - minX) * i / 4);
    distributionCtx.textAlign = "center";
    distributionCtx.textBaseline = "top";
    distributionCtx.fillStyle = "#5B5468";
    xTicks.forEach((value) => {
      const x = xPosition(value);
      distributionCtx.beginPath();
      distributionCtx.moveTo(x, padding.top + plotHeight);
      distributionCtx.lineTo(x, padding.top + plotHeight + 4);
      distributionCtx.stroke();
      distributionCtx.fillText(formatTick(value), x, padding.top + plotHeight + 8);
    });
    distributionCtx.font = '500 12px "Karla", sans-serif';
    distributionCtx.fillStyle = "#221D2E";
    distributionCtx.fillText("x", padding.left + plotWidth / 2, height - 11);

    if (isDiscrete) {
      const slotWidth = plotWidth / (maxX - minX);
      const barWidth = Math.max(1, slotWidth * .72);
      distributionCtx.fillStyle = "#D8579C";
      points.forEach((point) => {
        const x = xPosition(point.x) - barWidth / 2;
        const y = yPosition(point.y);
        distributionCtx.fillRect(x, y, barWidth, padding.top + plotHeight - y);
      });
    } else {
      distributionCtx.beginPath();
      points.forEach((point, index) => {
        const x = xPosition(point.x), y = yPosition(point.y);
        if (index === 0) distributionCtx.moveTo(x, padding.top + plotHeight);
        distributionCtx.lineTo(x, y);
      });
      distributionCtx.lineTo(xPosition(points[points.length - 1].x), padding.top + plotHeight);
      distributionCtx.closePath();
      distributionCtx.fillStyle = "rgba(216, 87, 156, .12)";
      distributionCtx.fill();
      distributionCtx.strokeStyle = "#D8579C";
      distributionCtx.lineWidth = 2.5;
      distributionCtx.stroke();
    }

    const label = type === "normal" ? "Probability density" : "Probability mass";
    distributionHint.textContent = `${label} · x is the ${type === "normal" ? "measured value" : "event count"}`;
    distributionCanvas.setAttribute("aria-label", `${type[0].toUpperCase() + type.slice(1)} distribution ${label.toLowerCase()} chart`);
  }

  function applyMode(mode) {
    const graphing = mode === "graphing";
    const distribution = mode === "distribution";
    scientificView.hidden = graphing || distribution;
    graphView.hidden = !graphing;
    distributionView.hidden = !distribution;
    calcEl.classList.toggle("graphing", graphing || distribution);
    calcEl.classList.toggle("distribution", distribution);
    calcEl.setAttribute("aria-label", graphing ? "2D graphing calculator" : distribution ? "Probability distribution explorer" : "Scientific calculator");
    if (graphing) drawGraph();
    if (distribution) drawDistribution();
  }

  const constellation = initConstellation();

  addFunctionButton.addEventListener("click", () => {
    if (graphFunctions.length >= MAX_GRAPH_FUNCTIONS) return;
    const fn = { id: nextGraphId++, expression: "", visible: true };
    graphFunctions.push(fn);
    renderGraphFunctions(fn.id);
    drawGraph();
  });

  $("resetGraph").addEventListener("click", () => {
    graphScale = 40;
    graphOffsetX = 0;
    graphOffsetY = 0;
    drawGraph();
  });
  $("graphSettings").addEventListener("click", () => settingsDialog.showModal());
  $("distributionSettings").addEventListener("click", () => settingsDialog.showModal());
  distributionSelect.addEventListener("change", renderDistributionControls);

  graphCanvas.addEventListener("pointerdown", (event) => {
    graphDrag = {
      pointerId: event.pointerId,
      x: event.clientX,
      y: event.clientY,
      offsetX: graphOffsetX,
      offsetY: graphOffsetY,
    };
    graphCanvas.setPointerCapture(event.pointerId);
  });

  graphCanvas.addEventListener("pointermove", (event) => {
    if (!graphDrag || graphDrag.pointerId !== event.pointerId) return;
    graphOffsetX = graphDrag.offsetX + event.clientX - graphDrag.x;
    graphOffsetY = graphDrag.offsetY + event.clientY - graphDrag.y;
    drawGraph();
  });

  graphCanvas.addEventListener("pointerup", () => { graphDrag = null; });
  graphCanvas.addEventListener("pointercancel", () => { graphDrag = null; });
  graphCanvas.addEventListener("wheel", (event) => {
    event.preventDefault();
    const rect = graphCanvas.getBoundingClientRect();
    const mouseX = event.clientX - rect.left;
    const mouseY = event.clientY - rect.top;
    const worldX = (mouseX - rect.width / 2 - graphOffsetX) / graphScale;
    const worldY = (rect.height / 2 + graphOffsetY - mouseY) / graphScale;
    const nextScale = Math.max(10, Math.min(240, graphScale * (event.deltaY < 0 ? 1.12 : 1 / 1.12)));
    graphOffsetX = mouseX - rect.width / 2 - worldX * nextScale;
    graphOffsetY = worldY * nextScale - (mouseY - rect.height / 2);
    graphScale = nextScale;
    drawGraph();
  }, { passive: false });

  modeSelect.addEventListener("change", () => {
    applyMode(modeSelect.value);
    settingsDialog.close();
  });
  stellarToggle.addEventListener("change", () => constellation.setEnabled(stellarToggle.checked));
  $("closeSettings").addEventListener("click", () => settingsDialog.close());
  settingsDialog.addEventListener("click", (event) => {
    if (event.target === settingsDialog) settingsDialog.close();
  });
  window.addEventListener("resize", () => {
    if (!graphView.hidden) drawGraph();
    if (!distributionView.hidden) drawDistribution();
  });

  /* ---------- wiring ---------- */
  keysEl.addEventListener("click", (e) => {
    const b = e.target.closest("button");
    if (!b) return;
    switch (b.dataset.act) {
      case "ins": insert(s.inv && b.dataset.invIns ? b.dataset.invIns : b.dataset.ins, b.dataset.kind); break;
      case "decimal": decimal(); break;
      case "back": back(); break;
      case "clear": clearAll(); break;
      case "equals": equals(); break;
      case "recip": recip(); break;
      case "deg": s.deg = !s.deg; render(); break;
      case "inv": s.inv = !s.inv; render(); break;
      case "settings": settingsDialog.showModal(); break;
    }
  });

  const KEYMAP = { "+": "+", "-": "-", "*": "×", x: "×", "/": "÷", "^": "^" };
  const FNKEYS = { s: "sin(", c: "cos(", t: "tan(", l: "ln(", r: "sqrt(" };
  document.addEventListener("keydown", (e) => {
    if (e.ctrlKey || e.metaKey || e.altKey) return;
    if (e.target instanceof Element && e.target.closest("input, textarea, select, dialog")) return;
    const k = e.key;
    let sel = null;
    if (/^\d$/.test(k)) { insert(k, "num"); sel = `[data-ins="${k}"]`; }
    else if (k in KEYMAP) { e.preventDefault(); insert(KEYMAP[k], "op"); sel = `[data-ins="${KEYMAP[k]}"][data-kind="op"]`; }
    else if (k === "." || k === ",") { decimal(); sel = '[data-act="decimal"]'; }
    else if (k === "(") { insert("(", "open"); sel = '[data-kind="open"]'; }
    else if (k === ")") { insert(")", "close"); sel = '[data-kind="close"]'; }
    else if (k === "!") { insert("!", "post"); sel = '[data-ins="!"]'; }
    else if (k === "%") { insert("%", "post"); sel = '[data-ins="%"]'; }
    else if (k === "p") { insert("π", "const"); sel = '[data-ins="π"]'; }
    else if (k === "e") { insert("e", "const"); sel = '[data-ins="e"]'; }
    else if (k in FNKEYS) { insert(FNKEYS[k], "fn"); sel = `[data-ins="${FNKEYS[k]}"]`; }
    else if (k === "Enter" || k === "=") { e.preventDefault(); equals(); sel = '[data-act="equals"]'; }
    else if (k === "Backspace") { back(); sel = '[data-act="back"]'; }
    else if (k === "Escape") { clearAll(); sel = '[data-act="clear"]'; }
    if (sel) {
      const btn = keysEl.querySelector(sel);
      if (btn) { btn.classList.add("pressed"); setTimeout(() => btn.classList.remove("pressed"), 110); }
    }
  });

  renderGraphFunctions();
  renderDistributionControls();
  applyMode(modeSelect.value);
  render();
})();