(function(){
const LS_KEY='run-tracker-state';

function toQ(x){return Math.round(Number(x)*100);} // quantize to centi-percent
function fromQ(q){return q/100;}
function fmt(q){return fromQ(q).toFixed(2);}

function loadStateV2(){
  try{
    const raw=localStorage.getItem(LS_KEY);
    if(!raw) throw 0;
    const s=JSON.parse(raw);
    if(s.settings && s.settings.schemaVersion===2) return s;
  }catch(e){}
  return {runs:[], starts:{}, settings:{schemaVersion:2, defaultThresholdQ:200}}; // default +2%
}

function saveStateV2(){
  localStorage.setItem(LS_KEY, JSON.stringify(state));
}

let state = loadStateV2();

function getOrInitStart(startQ){
  const key=fmt(startQ);
  if(!state.starts[key]){
    state.starts[key]={startQ, blacklisted:false, thresholdQ:startQ+state.settings.defaultThresholdQ};
  }
  return state.starts[key];
}

function setStartThreshold(startQ, thresholdQ){
  const sp=getOrInitStart(startQ);
  const clamped=Math.min(10000, Math.max(thresholdQ, startQ));
  sp.thresholdQ=clamped;
}

function toggleStartBlacklist(startQ, flag){
  const sp=getOrInitStart(startQ);
  sp.blacklisted=!!flag;
}

function isIncluded(run, sp){
  if(sp.blacklisted) return {included:false, reason:'blacklist'};
  const maxQ = run.completed ? 10000 : (run.endQ ?? run.startQ);
  if(maxQ <= sp.thresholdQ) return {included:false, reason:'threshold'};
  return {included:true};
}

function aggregateChokepoints(runs){
  const failMap=new Map();
  const includedRuns=[];
  for(const r of runs){
    const sp=getOrInitStart(r.startQ);
    const inc=isIncluded(r, sp);
    r._included=inc.included;
    r._reason=inc.reason;
    if(inc.included){
      includedRuns.push(r);
      if(r.endQ!==undefined){
        const agg=failMap.get(r.endQ)||{pointQ:r.endQ,fails:0,passes:0};
        agg.fails++;
        failMap.set(r.endQ,agg);
      }
    }
  }
  const points=[...failMap.keys()];
  for(const r of includedRuns){
    for(const p of points){
      if(r.startQ < p && (r.completed || (r.endQ!==undefined && r.endQ>p))){
        const agg=failMap.get(p); agg.passes++; }
    }
  }
  return failMap;
}

function recompute(){
  for(const r of state.runs){ getOrInitStart(r.startQ); }
  const chokeMap=aggregateChokepoints(state.runs);
  renderSessions();
  renderStarts();
  renderChokepoints(chokeMap);
  saveStateV2();
}

function renderSessions(){
  const container=document.getElementById('tab_sessions');
  let html='<table><tr><th>Start %</th><th>End %</th><th>Included?</th></tr>';
  for(const r of state.runs.slice().sort((a,b)=>a.ts-b.ts)){
    const endStr=r.completed?'Finish':fmt(r.endQ);
    const inc=r._included?'Yes':'No';
    const reason=r._reason?` (${r._reason})`:'';
    html+=`<tr><td class="percent">${fmt(r.startQ)}</td><td class="percent">${endStr}</td><td>${inc}${reason}</td></tr>`;
  }
  html+='</table>';
  container.innerHTML=html;
}

function renderStarts(){
  const container=document.getElementById('tab_starts');
  let html=`<div>Default threshold offset %: <input id="defaultThreshold" type="number" step="0.01" value="${fmt(state.settings.defaultThresholdQ)}"></div>`;
  html+='<table><tr><th>Start %</th><th>Threshold %</th><th>Blacklisted</th></tr>';
  const entries=Object.values(state.starts).sort((a,b)=>a.startQ-b.startQ);
  for(const sp of entries){
    html+=`<tr><td class="percent">${fmt(sp.startQ)}</td>`+
          `<td><input data-start="${sp.startQ}" class="thresholdInput" type="number" step="0.01" value="${fmt(sp.thresholdQ)}"></td>`+
          `<td><input data-start="${sp.startQ}" class="blackInput" type="checkbox" ${sp.blacklisted?'checked':''}></td></tr>`;
  }
  html+='</table>';
  container.innerHTML=html;
  const def=document.getElementById('defaultThreshold');
  def.addEventListener('change',e=>{state.settings.defaultThresholdQ=toQ(parseFloat(e.target.value)||0);recompute();});
  container.querySelectorAll('.thresholdInput').forEach(inp=>{
    inp.addEventListener('change',e=>{const sQ=+e.target.getAttribute('data-start'); setStartThreshold(sQ,toQ(parseFloat(e.target.value)||0)); recompute();});
  });
  container.querySelectorAll('.blackInput').forEach(inp=>{
    inp.addEventListener('change',e=>{const sQ=+e.target.getAttribute('data-start'); toggleStartBlacklist(sQ,e.target.checked); recompute();});
  });
}

function renderChokepoints(map){
  const container=document.getElementById('tab_chokepoints');
  let html='<table><tr><th>Point %</th><th>Fails</th><th>Passes</th><th>Success Rate</th><th>Samples</th></tr>';
  const arr=[...map.values()].sort((a,b)=>b.fails-a.fails);
  for(const agg of arr){
    const samples=agg.fails+agg.passes;
    const rate=samples?(agg.passes/(samples)).toFixed(2):'0.00';
    html+=`<tr><td class="percent">${fmt(agg.pointQ)}</td><td class="percent">${agg.fails}</td><td class="percent">${agg.passes}</td><td class="percent">${rate}</td><td class="percent">${samples}</td></tr>`;
  }
  html+='</table>';
  container.innerHTML=html;
}

function parseInput(str){
  const s=str.trim();
  let m=s.match(/^(\d+(?:\.\d+)?)%-\s*(\d+(?:\.\d+)?)%$/i);
  if(m){
    return {startQ:toQ(parseFloat(m[1])), endQ:toQ(parseFloat(m[2])), completed:false};
  }
  m=s.match(/^(\d+(?:\.\d+)?)%-(?:100%|finish)$/i);
  if(m){
    return {startQ:toQ(parseFloat(m[1])), endQ:undefined, completed:true};
  }
  return null;
}

function addRunFromInput(){
  const input=document.getElementById('runInput');
  const parsed=parseInput(input.value);
  if(!parsed){alert('Bad input'); return;}
  state.runs.push({id:String(Date.now()), startQ:parsed.startQ, endQ:parsed.endQ, completed:parsed.completed, ts:Date.now()});
  input.value='';
  recompute();
}

document.getElementById('addRunBtn').addEventListener('click',addRunFromInput);

const nav=document.getElementById('navTabs');
nav.addEventListener('click',e=>{
  if(e.target.tagName!=='BUTTON') return;
  const tab=e.target.getAttribute('data-tab');
  ['sessions','chokepoints','starts'].forEach(t=>{
    document.getElementById('tab_'+t).style.display = t===tab?'block':'none';
  });
});

recompute();

})();
