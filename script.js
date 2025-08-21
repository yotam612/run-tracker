// Run Progress Tracker logic
    let parts = [], runs = [], runDataRaw = "";
    let allRunsMemory = [];
    let importLogs = [];
    let currentSaveFile = null;
    let days = {}; let currentDay = null;
    let selectedRunName = null;

    const formatRange = (from, to) => `${from}% - ${to}%`;


    /**
     * Geometry Dash run scheduler (efficient, O(n) + pruning).
     *
     * Input:
     *  - successRates: array of per-part success probabilities in [0,1].
     *  - threshold: success coefficient in [0,1] (e.g., 0.10 for 10%).
     *  - opts (optional):
     *      - epsilon: clamp floor for probabilities; default 1e-12.
     *      - oneBased: if true, returns 1-based indices; default false.
     *
     * Rules enforced:
     *  - Runs are contiguous (neighbors only).
     *  - For each start i, keep only the maximal run starting at i whose
     *    product(probabilities) >= threshold. If even part i alone is < threshold,
     *    still keep the singleton [i, i].
     *  - After constructing one maximal run per start, remove any run that is fully
     *    contained in another run (full-overlap pruning). Partial overlaps allowed.
     *
     * Probability model:
     *  - Independence assumption: P(run) = Π p_k for parts in the run.
     *  - Computed via log-sums to avoid underflow.
     */
    function scheduleRuns(successRates, threshold, opts = {}) {
      const epsilon = opts.epsilon ?? 1e-12;
      const oneBased = !!opts.oneBased;

      if (!Array.isArray(successRates) || successRates.length === 0) {
        return [];
      }
      if (!(threshold > 0 && threshold <= 1)) {
        throw new Error("threshold must be in (0,1]. Use 0.10 for 10%.");
      }

      const n = successRates.length;
      const clamp = (x, lo, hi) => Math.min(Math.max(x, lo), hi);

      // Precompute log probabilities (all <= 0)
      const logP = new Array(n);
      for (let i = 0; i < n; i++) {
        const p = clamp(successRates[i], epsilon, 1);
        logP[i] = Math.log(p);
      }
      const logT = Math.log(clamp(threshold, epsilon, 1));

      // Two-pointer expansion to get one maximal run per start index i
      // sumLog represents log product over [i..j] when j >= i
      let j = -1;
      let sumLog = 0;
      const runs = []; // {start, end, logProb}

      for (let i = 0; i < n; i++) {
        if (j < i - 1) {
          // Reset window to empty before i
          j = i - 1;
          sumLog = 0;
        }

        // Try to extend j as far as threshold allows for this i
        while (j + 1 < n && sumLog + logP[j + 1] >= logT) {
          j++;
          sumLog += logP[j];
        }

        if (j >= i) {
          // Found a maximal run [i..j] s.t. product >= threshold
          runs.push({ start: i, end: j, logProb: sumLog });
          // Prepare for next i: shrink window from the left
          sumLog -= logP[i];
        } else {
          // Even single part i is below threshold; keep singleton by rule
          runs.push({ start: i, end: i, logProb: logP[i] });
          // j < i, nothing to subtract (window is empty)
        }
      }

      // Full containment pruning:
      // Remove any run that is fully contained within another run.
      // Sort by length DESC, then by start ASC for deterministic behavior.
      runs.sort((a, b) => {
        const lenA = a.end - a.start;
        const lenB = b.end - b.start;
        if (lenA !== lenB) return lenB - lenA;
        return a.start - b.start;
      });

      const kept = [];
      for (const r of runs) {
        let contained = false;
        for (const k of kept) {
          if (k.start <= r.start && k.end >= r.end) {
            contained = true;
            break;
          }
        }
        if (!contained) kept.push(r);
      }

      // Format output
      return kept
        .sort((a, b) => a.start - b.start || a.end - b.end) // optional: sort by start
        .map(r => ({
          start: oneBased ? r.start + 1 : r.start,
          end: oneBased ? r.end + 1 : r.end,
          prob: Math.exp(r.logProb) // run success probability (product)
        }));
    }


    function computeStatForRange(run, range) {
      const overlaps = run.from <= range.from && run.to >= range.from;
      const pass = run.to > range.to || run.to === 100;
      return overlaps ? { attempts: run.count, passes: pass ? run.count : 0 } : { attempts: 0, passes: 0 };
    }


    function parseRuns(input) {
      const lines = input.split(/\r?\n/).map(l => l.trim()).filter(l => l);
      const parsed = [];
      for (const line of lines) {
        let match = line.match(/(\d+)%\s*-\s*(\d+)%\s*x(\d+)/);
        if (match) {
          parsed.push({ from: +match[1], to: +match[2], count: +match[3], raw: line }); continue;
        }
        match = line.match(/(\d+)%\s*x(\d+)/);
        if (match) {
          parsed.push({ from: 0, to: +match[1], count: +match[2], raw: line });
        }
      }
      return parsed;
    }


    // ————————————————
    // Helpers
    // ————————————————

    /**
     * Does run overlap the range at all?
     */
    function isAttempt(run, range) {
      return run.from <= range.from && run.to >= range.from;
    }


    /**
     * Does run fully cover the range?
     */
    function isPass(run, range) {
      if (range.to === 100) {
        return run.from <= range.from && run.to >= 100;
      }
      return run.from <= range.from && run.to > range.to;
    }

        // NEW — returns a strictly decreasing, normalized weight array of length N.
    // Uses a log-based (power-law via log) shape so that the first 20 weights sum ≈ 0.8.
    function generateLogWeights(N = 100, c = 3.5, p = 1.6) {
      // raw[i] = 1 / (i + c)^p  = exp( -p * log(i + c) )
      const raw = new Array(N);
      for (let i = 0; i < N; i++) {
        raw[i] = 1 / Math.pow(i + c, p);
      }
      const sum = raw.reduce((a, b) => a + b, 0);
      const w = raw.map(x => x / sum);

      // Monotonicity guard (strictly decreasing)
      for (let i = 1; i < w.length; i++) {
        if (!(w[i - 1] > w[i])) {
          // enforce strict decrease in the unlikely event of float ties
          w[i] = Math.min(w[i], Math.nextAfter(w[i - 1], 0));
        }
      }
      return w;
    }

    // NEW — memoized accessor for the weights
    function getLogWeights() {
      if (!window._logWeights || !Array.isArray(window._logWeights) || window._logWeights.length !== 100) {
        window._logWeights = generateLogWeights(100, 3.5, 1.6); // ≈80% mass in first 20 points
      }
      return window._logWeights;
    }

    /**
     * Accumulate attempts & passes by walking batches in order.
     * Stops once attempts ≥ minAttempts (unless minAttempts is Infinity).
     * Returns { attempts, passes, usedBatches }.
     */


    // Counts total attempts for a specific range across all batches.
    // Attempts are counted by run.count for runs that overlap the range.
    function countTotalAttemptsForRange(range, batches) {
      let total = 0;
      for (const batch of batches) {
        for (const run of batch.data) {
          if (isAttempt(run, range)) {
            total += run.count; // every pass is also an attempt
          }
        }
      }
      return total; // dynamic kernel length
    }

    // Builds a monotone-decreasing kernel of length N where the first 20% of points
    // sum to ~80% of the total (within tiny error). Newest position is index 0.
    // We solve for exponent p in w[i] ∝ 1/(i+1)^p via bisection, then normalize.
    function buildDynamicKernel80_20(N) {
      if (N <= 0) return [];
      if (N === 1) return [1];

      const m = Math.max(1, Math.round(0.2 * N)); // number of points in the first 20%
      const target = 0.80;

      function ratioForP(p) {
        let top = 0, total = 0;
        for (let i = 1; i <= N; i++) {
          const w = 1 / Math.pow(i, p);
          total += w;
          if (i <= m) top += w;
        }
        return top / total;
      }

      // Bisection: ratio increases with p (more mass on the front).
      let lo = 0.01, hi = 10.0;
      for (let iter = 0; iter < 60; iter++) {
        const mid = (lo + hi) / 2;
        const r = ratioForP(mid);
        if (r < target) lo = mid; else hi = mid;
      }
      const p = (lo + hi) / 2;

      // Unnormalized newest→oldest weights, then normalize to sum 1.
      const w = new Array(N);
      let sum = 0;
      for (let i = 1; i <= N; i++) {
        const v = 1 / Math.pow(i, p);
        w[i - 1] = v;
        sum += v;
      }
      for (let i = 0; i < N; i++) w[i] /= sum;

      return w;
    }

    // Newest→oldest. Includes whole batches until attempts >= capAttempts.
    // Simple average (all attempts equal). No splitting of batches.
    function accumulateWindowUnweightedNoSplit(range, batchesDesc, capAttempts = 100) {
      let attempts = 0, passes = 0, usedBatches = 0;

      for (const batch of batchesDesc) {
        let ba = 0, bp = 0;
        for (const run of batch.data) {
          if (!isAttempt(run, range)) continue;
          ba += run.count;
          if (isPass(run, range)) bp += run.count;
        }
        if (ba === 0) continue;

        attempts += ba;
        passes   += bp;
        usedBatches += 1;

        if (attempts >= capAttempts) break; // allow going over due to last whole batch
      }

      const rate = attempts ? +(100 * passes / attempts).toFixed(1) : 0;
      return { attempts, passes, rate, usedBatches };
    }
        
    // Sessions tab — Overall stats (no diff).
    // Parts use weighted window (~100 attempts, no split).
    // Runs use simple unweighted window (~100 attempts, no split).
    function buildSessionsOverallStats(parts, runs, importLogs) {
      const batchesDesc = [...importLogs].reverse(); // newest → oldest

      // Parts (weighted)
      const partStats = parts.map(part => {
        const cur = accumulateWeightedDynamic(part, batchesDesc);
        return {
          name: part.name,
          attempts: cur.attempts,
          passes: cur.passes,
          rate: cur.weightedRate, // percent
        };
      });

      // Runs (simple)
      const runStats = runs.map(run => {
        const cur = accumulateWindowUnweightedNoSplit(run, batchesDesc, 100);
        return {
          name: run.name,
          attempts: cur.attempts,
          passes: cur.passes,
          rate: cur.rate, // percent
        };
      });

      return [...partStats, ...runStats].sort((a,b)=>a.rate-b.rate);
    }



    // Sessions tab — Latest session stats (no diff).
    function buildSessionsSessionStats(parts, runs, importLogs) {
      if (!importLogs.length) return [];
      const allRanges = [...parts, ...runs];
      const latest = importLogs[importLogs.length - 1].data;

      return allRanges.map(range => {
        const cur = accumulate(range, [{ data: latest }], Infinity);
        if (cur.attempts === 0) return null;
        const rate = +(100 * cur.passes / cur.attempts).toFixed(1);
        return { name: range.name, attempts: cur.attempts, passes: cur.passes, rate };
      }).filter(Boolean).sort((a,b)=>a.rate-b.rate);
    }


    // Trends tab — Overall stats with comparison (simple average, no weighting).
    // "Current" = most recent ~100 attempts (whole batches only).
    // "Previous" = next ~100 attempts after the current window (whole batches only).
    function buildTrendsOverallStats(parts, runs, importLogs) {
      const allRanges = [...parts, ...runs];
      const batchesDesc = [...importLogs].reverse(); // newest → oldest

      return allRanges.map(range => {
        const cur  = accumulateWindowUnweightedNoSplit(range, batchesDesc, 100);
        const prev = accumulateWindowUnweightedNoSplit(range, batchesDesc.slice(cur.usedBatches), 100);

        const rate = cur.rate;
        const prevRate = prev.attempts ? prev.rate : null;
        const diffText = prevRate !== null
          ? ` (${(rate - prevRate > 0 ? '+' : '') + (rate - prevRate).toFixed(1)}%)`
          : '';

        return {
          name: range.name,
          attempts: cur.attempts,
          passes: cur.passes,
          rate,
          diffText
        };
      }).sort((a,b)=>a.rate-b.rate);
    }

    // Trends tab — Daily stats with comparison to previous day (simple average).
    // This mirrors your existing buildDailyStats; exposed under a trends-specific name.
    function buildTrendsDailyStats(parts, runs, importLogs, currentDay) {
      const allRanges = [...parts, ...runs];
      const dayKeys   = Object.keys(days);
      const idx       = currentDay ? dayKeys.indexOf(currentDay) : -1;
      const prevDay   = idx > 0 ? dayKeys[idx - 1] : null;

      const todayBatches = importLogs.filter(l => l.day === currentDay);
      const prevBatches  = prevDay ? importLogs.filter(l => l.day === prevDay) : [];

      return allRanges.map(range => {
        const cur  = accumulate(range, todayBatches, Infinity);
        const prev = accumulate(range, prevBatches, Infinity);
        if (cur.attempts === 0) return null;

        const rate   = +(100 * cur.passes / cur.attempts).toFixed(1);
        const prevRT = prev.attempts ? +(100 * prev.passes / prev.attempts).toFixed(1) : null;
        const diff   = prevRT !== null ? +(rate - prevRT).toFixed(1) : null;

        return {
          name:     range.name,
          attempts: cur.attempts,
          passes:   cur.passes,
          rate,
          diffText: diff !== null ? ` (${diff > 0 ? '+' : ''}${diff}%)` : ''
        };
      }).filter(Boolean).sort((a,b)=>a.rate-b.rate);
    }



    // Weighted accumulator with a hard ~100-attempt window that DOES NOT split batches.
    // It includes newest batches until the first time the running attempts >= 100,
    // allowing the last included batch to push the total over 100, then stops.
    // Kernel length = total attempts of the included batches.
    // First 20% of kernel mass = 80% (via buildDynamicKernel80_20).
    function accumulateWeightedDynamic(range, batchesDesc) {
      // PHASE 1 — choose batches without splitting, up to the first crossing of 100 attempts
      const chosen = []; // [{ attempts, passes }]
      let totalAttempts = 0;

      for (const batch of batchesDesc) {
        // count relevant attempts/passes in this batch
        let ba = 0, bp = 0;
        for (const run of batch.data) {
          if (!isAttempt(run, range)) continue;
          ba += run.count;
          if (isPass(run, range)) bp += run.count;
        }
        if (ba === 0) continue;

        chosen.push({ attempts: ba, passes: bp });
        totalAttempts += ba;

        // stop immediately after the first time we meet/exceed 100 attempts
        if (totalAttempts >= 100) break;
      }

      if (totalAttempts === 0) {
        return { attempts: 0, passes: 0, weightedRate: 0, usedBatches: 0 };
      }

      // PHASE 2 — build kernel of size = totalAttempts (may be >100 due to last batch)
      const K = buildDynamicKernel80_20(totalAttempts);

      // PHASE 3 — assign mean of the next K-slice to each chosen batch (no splitting)
      let cursor = 0;
      let rawAttempts = 0, rawPasses = 0;
      let wAttempts = 0, wPasses = 0;

      for (const { attempts: ba, passes: bp } of chosen) {
        const start = cursor;
        const end = Math.min(cursor + ba, totalAttempts); // defensive; should exactly fit by construction
        const size = end - start;

        let sliceSum = 0;
        for (let i = start; i < end; i++) sliceSum += K[i];
        const wBatch = size > 0 ? (sliceSum / size) : 0;

        rawAttempts += ba;
        rawPasses += bp;
        wAttempts += wBatch * ba;
        wPasses += wBatch * bp;

        cursor = end;
      }

      const weightedRate = wAttempts > 0 ? +(100 * (wPasses / wAttempts)).toFixed(1) : 0;

      return {
        attempts: rawAttempts,              // may be > 100 due to last batch
        passes: rawPasses,
        weightedRate,
        usedBatches: chosen.length
      };
    }


    // Unweighted accumulator: walks batches (any order), stopping after minAttempts.
    // Returns raw attempts/passes and the number of batches used.
    // No weighting here; weighted path is handled by accumulateWeightedDynamic.
    function accumulate(range, batches, minAttempts = Infinity) {
      let rawAttempts = 0;
      let rawPasses = 0;
      let usedBatches = 0;

      for (const batch of batches) {
        let batchAttempts = 0;
        let batchPasses = 0;

        for (const run of batch.data) {
          if (!isAttempt(run, range)) continue;
          batchAttempts += run.count;
          if (isPass(run, range)) {
            batchPasses += run.count;
          }
        }

        if (batchAttempts === 0) continue;

        rawAttempts += batchAttempts;
        rawPasses += batchPasses;
        usedBatches++;

        if (rawAttempts >= minAttempts) break;
      }

      return {
        attempts: rawAttempts,
        passes: rawPasses,
        usedBatches
      };
    }

    // ————————————————
    // Stat-builders
    // ————————————————

    function render(stats, containerId, showDiff = false) {
      const container = document.getElementById(containerId);
      container.innerHTML = '';

      const isRunPanel  = containerId.includes('Runs');
      const inTrendsTab = containerId.startsWith('trends') || containerId.includes('Trends');

      stats.forEach(s => {
        const div = document.createElement('div');
        div.className = 'stat-item';

        const baseText = showDiff
          ? `${s.name}: ${s.passes}/${s.attempts} (${s.rate}%)${s.diffText || ''}`
          : `${s.name}: ${s.passes}/${s.attempts} (${s.rate}%)`;

        const label = document.createElement('span');
        label.textContent = baseText;
        div.appendChild(label);

        if (isRunPanel) {
          div.style.cursor = 'pointer';
          if (s.name === selectedRunName) {
            div.style.fontWeight = 'bold';
            div.style.backgroundColor = '#eef';
            div.style.borderRadius = '4px';
          }
          div.addEventListener('click', (e) => {
            if (e.target.tagName === 'INPUT') return;
            selectedRunName = (selectedRunName === s.name) ? null : s.name;
            applyRunFilter();
          });
        }

        container.appendChild(div);
      });
    }





    // ————————————————
    // Main calculateStats()
    // ————————————————

    // Computes datasets for both tabs.
    // - Sessions: overall (no diff) + session (latest batch), honors weighted toggle.
    // - Trends: overall (current vs previous windows, simple average) + daily (with diff).

    // Computes datasets for both tabs and renders the trends chart.
    function calculateStats() {
      const batchesDesc = [...importLogs].reverse();

      const partStats = parts.map(part => {
        const cur = accumulateWeightedDynamic(part, batchesDesc);
        return {
          name: part.name,
          attempts: cur.attempts,
          passes: cur.passes,
          rate: cur.weightedRate,
        };
      });

      const successRates = partStats.map(p => p.rate / 100);
      const tInput = document.getElementById('runThresholdInput');
      const tPercent = tInput ? parseFloat(tInput.value) : 10;
      const t = isNaN(tPercent) ? 0.10 : tPercent / 100;
      const scheduled = scheduleRuns(successRates, t);
      runs = scheduled.map(r => ({
        name: formatRange(parts[r.start].from, parts[r.end].to),
        from: parts[r.start].from,
        to: parts[r.end].to,
      }));
      const runStats = scheduled.map(r => ({
        name: formatRange(parts[r.start].from, parts[r.end].to),
        attempts: 0,
        passes: 0,
        rate: +(r.prob * 100).toFixed(1),
      }));

      const sessionsOverall = [...partStats, ...runStats].sort((a,b)=>a.rate-b.rate);

      const partStatsLatest = buildSessionsSessionStats(parts, [], importLogs);
      const sessionsSession = [...partStatsLatest, ...runStats].sort((a,b)=>a.rate-b.rate);

      const trendsOverall = buildTrendsOverallStats(parts, [], importLogs);
      const trendsDaily   = currentDay ? buildTrendsDailyStats(parts, [], importLogs, currentDay) : [];

      window.sessionsOverall = sessionsOverall;
      window.sessionsSession = sessionsSession;
      window.trendsOverall   = trendsOverall;
      window.trendsDaily     = trendsDaily;

      window.overall = partStats;

      applyRunFilter();

      const series = computeTrendsLevelSeries(parts, importLogs, getTrendBatchLimit());
      renderTrendsLevelChart(series);
    }




    function applyRunFilter() {
      const runDef = runs.find(r => r.name === selectedRunName);

      const isPartName = (s) => parts.some(p => p.name === s.name);
      const isRunName  = (s) => runs.some(r => r.name === s.name);

      const filterBySelectedRun = (statsArray) => {
        if (!selectedRunName) return statsArray.filter(isPartName);
        return statsArray.filter(s => {
          const partDef = parts.find(p => p.name === s.name);
          return partDef && runDef && runDef.from <= partDef.from && runDef.to >= partDef.to;
        });
      };

      // --- Sessions tab (Overall) ---
      render(filterBySelectedRun((window.sessionsOverall || []).filter(isPartName)), 'sessionsPartsOverall', false);
      render((window.sessionsOverall || []).filter(isRunName),                            'sessionsRunsOverall',  false);

      // --- Sessions tab (Latest) ---
      render(filterBySelectedRun((window.sessionsSession || []).filter(isPartName)), 'sessionsPartsLatest', false);
      render((window.sessionsSession || []).filter(isRunName),                            'sessionsRunsLatest',  false);

      // --- Trends tab (Overall with diff) ---
      render(filterBySelectedRun((window.trendsOverall || []).filter(isPartName)),   'trendsPartsOverall',  true);

      // --- Trends tab (Daily with diff) ---
      render(filterBySelectedRun((window.trendsDaily || []).filter(isPartName)),     'trendsPartsDaily',    true);
    }



    function getDayDiff(name, currentRate) {
      if (!currentDay || !days[currentDay]) return '';
      const yesterday = Object.keys(days).reverse().find(d => d < currentDay);
      if (!yesterday || !days[yesterday][name]) return '';
      const prev = days[yesterday][name].rate;
      const diff = (currentRate - prev).toFixed(1);
      return ` (${diff > 0 ? '+' : ''}${diff}%)`;
    }



    function importRunData() {
      const input = document.getElementById('runData').value;
      const parsed = parseRuns(input);
      if (parsed.length === 0) return;

      // Add new log, assigning currentDay
      importLogs.push({
        timestamp: new Date().toLocaleString(),
        day: currentDay || null,
        data: parsed
      });

      // Update global memory
      allRunsMemory.push(...parsed);

      // Render and save
      renderLogs();
      calculateStats();
      saveToLocal();
    }


    function startNewDay() {
      const now = new Date();
      const dateStr = now.toLocaleDateString(undefined, { year: 'numeric', month: 'short', day: 'numeric' });

      const dayNumber = Object.keys(days).length + 1;
      const id = `Day ${dayNumber} | ${dateStr}`;

      if (!days[id]) {
        days[id] = {};
      }

      currentDay = id;
      updateDaySelect();
      calculateStats();
      saveToLocal();
    }

    function updateDaySelect() {
      const sel = document.getElementById('daySelect');
      const viewSel = document.getElementById('viewDaySelect');
      sel.innerHTML = '';
      viewSel.innerHTML = '<option value="">-- View Day Stats --</option>';

      Object.keys(days).forEach(d => {
        let opt = document.createElement('option');
        opt.value = d; opt.text = d;
        if (d === currentDay) opt.selected = true;
        sel.appendChild(opt);

        let viewOpt = document.createElement('option');
        viewOpt.value = d; viewOpt.text = d;
        viewSel.appendChild(viewOpt);
      });
    }

    function selectDay(day) {
      currentDay = day;
      calculateStats();
    }

    function toggleExpand(button) {
      const container = button.parentElement;
      const list = container.querySelector('.stats-list, .log-list, .part-list, .run-list');
      if (!list) return;

      if (list.style.maxHeight === 'none') {
        list.style.maxHeight = '200px';
        list.style.overflowY = 'auto';
        button.textContent = 'Expand';
      } else {
        list.style.maxHeight = 'none';
        list.style.overflowY = 'visible';
        button.textContent = 'Collapse';
      }
    }

    function renderLogs() {
      const c = document.getElementById('importLogs');
      c.innerHTML = '';

      // Show newest logs first
      for (let i = importLogs.length - 1; i >= 0; i--) {
        const log = importLogs[i];
        const displayIndex = i;

        const div = document.createElement('div');
        div.className = 'log-item';

        const dayText = log.day ? ` | ${log.day}` : '';

        div.innerHTML = `
          <strong>${log.timestamp}${dayText}</strong>
          <pre>${log.data.map(d => d.raw).join('\n')}</pre>
          <button onclick="deleteLog(${displayIndex})">Delete</button>
        `;

        c.appendChild(div);
      }
    }

    function deleteLog(i) {
      importLogs.splice(i, 1);
      allRunsMemory = importLogs.flatMap(log => log.data);
      renderLogs();
      calculateStats();
      saveToLocal();
    }

    function addPart() {
      const from = parseFloat(document.getElementById('partFrom').value);
      const to = parseFloat(document.getElementById('partTo').value);
      if (isNaN(from) || isNaN(to)) return;
      parts.push({ name: formatRange(from, to), from, to });
      renderParts(); calculateStats(); saveToLocal();
    }

    function renderParts() {
      const c = document.getElementById('partList');
      c.innerHTML = '';
      parts.forEach((p, i) => {
        let div = document.createElement('div');
        div.className = 'part-item';
        div.dataset.index = i; // Important for reordering
        div.innerHTML = `
          ${formatRange(p.from, p.to)}
          <button onclick="editPart(${i})">Edit</button>
          <button onclick="deletePart(${i})">Delete</button>
        `;
        c.appendChild(div);
      });

      Sortable.create(document.getElementById('partList'), {
        animation: 150,
        onEnd: function () {
          const newOrder = [];
          const items = document.querySelectorAll('#partList .part-item');
          items.forEach(item => {
            const idx = parseInt(item.dataset.index);
            newOrder.push(parts[idx]);
          });
          parts = newOrder;
          renderParts();
          calculateStats();
          saveToLocal();
        }
      });
    }

    function deletePart(i) {
      parts.splice(i, 1);
      renderParts(); calculateStats(); saveToLocal();
    }

    function editPart(i) {
      const from = parseFloat(prompt("New 'from' value:", parts[i].from));
      const to = parseFloat(prompt("New 'to' value:", parts[i].to));
      if (isNaN(from) || isNaN(to)) return;
      parts[i] = { name: formatRange(from, to), from, to };
      renderParts(); calculateStats(); saveToLocal();
    }

    function movePart(i, dir) {
      const j = i + dir;
      if (j < 0 || j >= parts.length) return;
      [parts[i], parts[j]] = [parts[j], parts[i]];
      renderParts(); saveToLocal();
    }

    function undoNewDay() {
      const dayKeys = Object.keys(days);
      if (dayKeys.length === 0) return;

      const last = dayKeys[dayKeys.length - 1];
      delete days[last];

      currentDay = Object.keys(days).pop() || null;

      updateDaySelect();
      calculateStats();
      saveToLocal();
    }



    function setupSaveFilePrompt() {
      const c = document.getElementById('saveFileUI');
      c.innerHTML = '<h2>Select or Create Save File</h2>';
      const sel = document.createElement('select');
      const keys = Object.keys(localStorage).filter(k => k.startsWith('runTracker_'));
      const def = document.createElement('option');
      def.text = '-- Select Save File --'; def.value = '';
      sel.appendChild(def);
      keys.forEach(key => {
        const name = key.replace('runTracker_', '');
        const o = document.createElement('option');
        o.text = name; o.value = name;
        sel.appendChild(o);
      });
      sel.onchange = () => { if (sel.value) loadFromLocal(sel.value); };
      c.appendChild(sel);
      const b = document.createElement('button');
      b.textContent = 'Create New Save File';
      b.onclick = () => {
        const name = prompt('Enter new save file name:');
        if (!name) return;
        currentSaveFile = name;
        parts = []; runs = []; runDataRaw = "";
        allRunsMemory = []; importLogs = []; days = {}; currentDay = null;
        document.getElementById('runData').value = "";
        renderParts(); renderLogs(); updateDaySelect(); calculateStats(); saveToLocal();
      };

      c.appendChild(b);

      // Export Button
      const exportBtn = document.createElement('button');
      exportBtn.textContent = 'Export Save File';
      exportBtn.onclick = () => {
        if (!currentSaveFile) return;
        const data = localStorage.getItem('runTracker_' + currentSaveFile);
        const blob = new Blob([data], { type: 'application/json' });
        const a = document.createElement('a');
        a.href = URL.createObjectURL(blob);
        a.download = currentSaveFile + '.json';
        a.click();
      };
      c.appendChild(exportBtn);

      // Import Button
      const importBtn = document.createElement('button');
      importBtn.textContent = 'Import Save File';
      importBtn.onclick = () => {
        const input = document.createElement('input');
        input.type = 'file';
        input.accept = '.json';
        input.onchange = e => {
          const file = e.target.files[0];
          if (!file) return;
          const reader = new FileReader();
          reader.onload = () => {
            try {
              const data = JSON.parse(reader.result);
              const name = prompt('Enter name for imported save file:');
              if (!name) return;
              localStorage.setItem('runTracker_' + name, JSON.stringify(data));
              setupSaveFilePrompt(); // refresh dropdown
              alert('Save file imported.');
            } catch (e) {
              alert('Invalid file.');
            }
          };
          reader.readAsText(file);
        };
        input.click();
      };
      c.appendChild(importBtn);

    }

    function saveToLocal() {
      if (!currentSaveFile) return;
      const d = { parts, allRunsMemory, importLogs, days, currentDay };
      localStorage.setItem('runTracker_' + currentSaveFile, JSON.stringify(d));
    }

    function loadFromLocal(name) {
      const d = JSON.parse(localStorage.getItem('runTracker_' + name));
      if (!d) return;
      parts = d.parts || [];
      runs = [];
      allRunsMemory = d.allRunsMemory || [];
      importLogs = d.importLogs || [];
      days = d.days || {};
      currentDay = d.currentDay || null;
      currentSaveFile = name;
      document.getElementById('runData').value = "";
      renderParts(); renderLogs(); updateDaySelect(); calculateStats();
    }


    function showTab(id) {
      document.querySelectorAll('.tab-content').forEach(el => el.classList.remove('active'));
      document.getElementById('tab_' + id).classList.add('active');
    }

    function renderDayStats(day) {
      const dayStatsDiv = document.getElementById('dayStats');
      dayStatsDiv.innerHTML = '';
      if (!day || !days[day]) return;

      const stats = days[day];
      const keys = Object.keys(stats).sort();
      for (const key of keys) {
        const stat = stats[key];
        const diff = getDayDiff(key, stat.rate);
        const text = `${key}: ${stat.passes}/${stat.attempts} (${stat.rate}%)${diff}`;
        let div = document.createElement('div');
        div.className = 'stat-item';
        div.textContent = text;
        dayStatsDiv.appendChild(div);
      }
    }


    // Formats a probability y (0..1) as a percent string with TWO significant digits
    // *after the leading zeros*. Example:
    //   y=0.000347  -> 0.0347% -> "0.035%"
    //   y=0.01234   -> 1.234%  -> "1.2%"
    //   y=0.4567    -> 45.67%  -> "46%"
    // This is effectively 2 significant digits on the percent value.
    function formatPercentSig2(y) {
      if (!isFinite(y) || y <= 0) return "0%";
      const x = y * 100; // percent
      const log10 = Math.log10(x);
      const dec = Math.max(0, 2 - 1 - Math.floor(log10)); // digits after decimal to keep 2 sig figs
      const capped = Math.min(dec, 10); // prevent overly long tails
      return x.toFixed(capped) + "%";
    }

    // For each batch index i (oldest→newest), build a window consisting of the
    // most recent ~100 attempts drawn from batches 0..i (no splitting), compute
    // per-part rates over that window, and push the product across parts.
    // Skips points until every part has at least 1 attempt in its window.
    function computeTrendsLevelSeries(parts, importLogs, batchLimit = Infinity) {
      if (!parts.length || !importLogs.length) return [];

      const logs = (batchLimit && batchLimit < importLogs.length)
        ? importLogs.slice(-batchLimit)
        : importLogs;
      const offset = importLogs.length - logs.length;
      const series = [];

      // Walk chronological prefixes: batches[0..i]
      for (let i = 0; i < logs.length; i++) {
        const prefix = logs.slice(0, i + 1);
        const batchesDesc = prefix.slice().reverse(); // newest→oldest within the prefix

        // Per-part windowed rates
        let product = 1;
        for (const part of parts) {
          const { attempts, rate } = accumulatePartWindowNoSplit(part, batchesDesc, 100);
          if (!attempts || rate === null) { product = null; break; } // need data for every part
          product *= rate;
        }
        if (product === null) continue; // skip until all parts have data in the window

        series.push({ x: offset + i + 1, y: product });
      }

      return series;
    }

    function getTrendBatchLimit() {
      const input = document.getElementById('trendBatchLimit');
      if (!input) return 50;
      const v = parseInt(input.value, 10);
      return isNaN(v) ? Infinity : v;
    }

    function setTrendBatchAll() {
      const input = document.getElementById('trendBatchLimit');
      if (input) {
        input.value = '';
        calculateStats();
      }
    }


    // Renders the level-chance line with log/linear Y scaling.
    // Raw series.y are probabilities in [0,1]. Labels always show percents of raw y.
    function renderTrendsLevelChart(series) {
      const canvas = document.getElementById('trendsLevelChart');
      if (!canvas) return;
      const ctx = canvas.getContext('2d');
      const W = canvas.width, H = canvas.height;

      ctx.clearRect(0, 0, W, H);

      if (!series.length) {
        ctx.fillStyle = '#555';
        ctx.font = '12px sans-serif';
        ctx.fillText('No trend data yet (need at least one attempt for every part).', 10, 20);
        canvas.onmousemove = null;
        canvas.onmouseleave = null;
        return;
      }

      // Prepare transformed values
      const eps = 1e-12;
      const useLog = (window.trendsScale === 'log');

      // Compute bounds on RAW y (for labels)
      let rawMin = Infinity, rawMax = -Infinity;
      for (const p of series) {
        if (p.y < rawMin) rawMin = p.y;
        if (p.y > rawMax) rawMax = p.y;
      }
      if (rawMin === rawMax) {
        const d = Math.max(1e-6, rawMax * 0.1);
        rawMin = Math.max(0, rawMax - d);
        rawMax = Math.min(1, rawMax + d);
      }

      // Transform for plotting
      const plotVals = series.map(p => useLog ? Math.log10(Math.max(p.y, eps)) : p.y);
      let plotMin = Math.min(...plotVals), plotMax = Math.max(...plotVals);
      if (plotMin === plotMax) {
        const d = useLog ? 0.5 : Math.max(1e-6, plotMax * 0.1);
        plotMin = plotMax - d;
      }

      // Plot area
      const L = 56, R = 10, T = 10, B = 30;
      const PW = W - L - R, PH = H - T - B;

      // Axes
      ctx.strokeStyle = '#999'; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.moveTo(L, T); ctx.lineTo(L, H - B); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(L, H - B); ctx.lineTo(W - R, H - B); ctx.stroke();

      // Y labels (top/bottom using RAW y)
      ctx.fillStyle = '#333';
      ctx.font = '12px sans-serif';
      ctx.textBaseline = 'middle';
      ctx.textAlign = 'left';
      ctx.fillText(formatPercentSig2(rawMax), 6, T + 6);
      ctx.fillText(formatPercentSig2(rawMin), 6, H - B);
      // Scale indicator
      ctx.fillText(window.trendsScale === 'log' ? 'log' : 'linear', W - 46, T + 6);

      // Mappers
      const xMin = series[0].x, xMax = series[series.length - 1].x, xSpan = Math.max(1, xMax - xMin);
      const xToPx = (x) => L + ((x - xMin) / xSpan) * PW;
      const yToPx = (valRaw) => {
        const v = useLog ? Math.log10(Math.max(valRaw, eps)) : valRaw;
        return T + (1 - (v - plotMin) / (plotMax - plotMin)) * PH;
      };

      // Line
      ctx.strokeStyle = '#1f77b4'; ctx.lineWidth = 2; ctx.beginPath();
      for (let i = 0; i < series.length; i++) {
        const px = xToPx(series[i].x);
        const py = yToPx(series[i].y);
        if (i === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
      }
      ctx.stroke();

      // Points
      ctx.fillStyle = '#1f77b4';
      const points = series.map(p => ({ x: p.x, y: p.y, px: xToPx(p.x), py: yToPx(p.y) }));
      for (const p of points) { ctx.beginPath(); ctx.arc(p.px, p.py, 2.5, 0, Math.PI * 2); ctx.fill(); }

      // Hover
      function redrawBase() {
        ctx.clearRect(0,0,W,H);
        ctx.strokeStyle = '#999'; ctx.lineWidth = 1;
        ctx.beginPath(); ctx.moveTo(L, T); ctx.lineTo(L, H - B); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(L, H - B); ctx.lineTo(W - R, H - B); ctx.stroke();
        ctx.fillStyle = '#333'; ctx.font = '12px sans-serif'; ctx.textBaseline='middle'; ctx.textAlign='left';
        ctx.fillText(formatPercentSig2(rawMax), 6, T + 6);
        ctx.fillText(formatPercentSig2(rawMin), 6, H - B);
        ctx.fillText(window.trendsScale === 'log' ? 'log' : 'linear', W - 46, T + 6);
        ctx.strokeStyle = '#1f77b4'; ctx.lineWidth = 2; ctx.beginPath();
        for (let i = 0; i < points.length; i++) {
          if (i === 0) ctx.moveTo(points[i].px, points[i].py); else ctx.lineTo(points[i].px, points[i].py);
        }
        ctx.stroke();
        ctx.fillStyle = '#1f77b4'; for (const p of points) { ctx.beginPath(); ctx.arc(p.px,p.py,2.5,0,Math.PI*2); ctx.fill(); }
      }
      function nearest(mx){ let bi=0,bd=1e9; for(let i=0;i<points.length;i++){const d=Math.abs(points[i].px-mx); if(d<bd){bd=d; bi=i;}} return points[bi]; }
      function tooltip(p){
        redrawBase();
        ctx.strokeStyle='#bbb'; ctx.lineWidth=1; ctx.beginPath(); ctx.moveTo(p.px,T); ctx.lineTo(p.px,H-B); ctx.stroke();
        ctx.fillStyle='#d62728'; ctx.beginPath(); ctx.arc(p.px,p.py,3.5,0,Math.PI*2); ctx.fill();
        const txt=`Batch ${p.x}: ${formatPercentSig2(p.y)}`;
        ctx.font='12px sans-serif'; const pad=6; const tw=ctx.measureText(txt).width; const th=18;
        let tx=Math.min(Math.max(p.px+8, L+2), W-R-tw-pad*2), ty=Math.min(Math.max(p.py-th-8, T+2), H-B-th-2);
        ctx.fillStyle='rgba(255,255,255,0.95)'; ctx.strokeStyle='#333'; ctx.lineWidth=1;
        ctx.beginPath(); ctx.rect(tx,ty,tw+pad*2,th); ctx.fill(); ctx.stroke();
        ctx.fillStyle='#000'; ctx.fillText(txt, tx+pad, ty+th/2+4);
      }
      redrawBase();
      canvas.onmousemove=(e)=>{const r=canvas.getBoundingClientRect(); const mx=e.clientX-r.left, my=e.clientY-r.top; if(mx<L||mx>W-R||my<T||my>H-B){redrawBase(); return;} tooltip(nearest(mx));};
      canvas.onmouseleave=()=>{redrawBase();};
    }


    // Newest→oldest. Includes whole batches until attempts >= capAttempts.
    // Returns simple rate for a single PART over that window.
    function accumulatePartWindowNoSplit(part, batchesDesc, capAttempts = 100) {
      let attempts = 0, passes = 0;

      for (const batch of batchesDesc) {
        let ba = 0, bp = 0;
        for (const run of batch.data) {
          if (!isAttempt(run, part)) continue;
          ba += run.count;
          if (isPass(run, part)) bp += run.count;
        }
        if (ba === 0) continue;

        attempts += ba;
        passes   += bp;

        if (attempts >= capAttempts) break; // allow going over due to last whole batch
      }

      return { attempts, passes, rate: attempts ? (passes / attempts) : null };
    }

    // Default chart scale for Trends level chart
    window.trendsScale = 'log'; // 'log' | 'linear'

    // Toggle handler (call once on load after DOM is ready)
    function setupTrendScaleToggle() {
      const btn = document.getElementById('toggleTrendScale');
      if (!btn) return;
      btn.textContent = 'Scale: Log';
      btn.onclick = () => {
        window.trendsScale = (window.trendsScale === 'log') ? 'linear' : 'log';
        btn.textContent = 'Scale: ' + (window.trendsScale === 'log' ? 'Log' : 'Linear');
        // re-render chart with current series
        const series = computeTrendsLevelSeries(parts, importLogs, getTrendBatchLimit());
        renderTrendsLevelChart(series);
      };
    }


    // Ensure UI and stats initialize once.
    window.onload = () => {
      setupSaveFilePrompt();
      showTab('input');
      calculateStats();
      setupTrendScaleToggle(); // wire the Trends chart scale toggle
      const tInput = document.getElementById('runThresholdInput');
      if (tInput) tInput.addEventListener('change', calculateStats);
      const bInput = document.getElementById('trendBatchLimit');
      if (bInput) bInput.addEventListener('change', calculateStats);
    };



