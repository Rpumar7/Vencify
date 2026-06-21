import { useState, useEffect, useRef, useCallback } from "react";

// ═══════════════════════════════════════════════════════════════════
// TOKENS
// ═══════════════════════════════════════════════════════════════════
const T = {
  bg:"#080A09", surf:"#0E1110", surf2:"#131615", surf3:"#181B19",
  border:"#1A1D1B", bord2:"#222724",
  accent:"#00D4A0", accDim:"#00D4A00E", accGlow:"#00D4A024",
  red:"#FF5252",    redDim:"#FF525210",
  yellow:"#FFB300", yelDim:"#FFB30010",
  blue:"#4D9EFF",   blueDim:"#4D9EFF10",
  purple:"#A78BFA", purDim:"#A78BFA10",
  orange:"#FF8C42", oraDim:"#FF8C4210",
  txt:"#E6ECEA", txtSub:"#6E7F79", txtMuted:"#323836",
  mono:"'JetBrains Mono','Fira Mono','Consolas',monospace",
};

// ═══════════════════════════════════════════════════════════════════
// DATA MODEL
// ═══════════════════════════════════════════════════════════════════
//
// PRODUCTO (catalog entry — no stock here):
//   { id, barcode, name, category, minStock, createdAt }
//
// LOTE (batch — stock lives here):
//   { id, productId, expiry, qty, createdAt }
//   One product can have MULTIPLE batches with different expiry dates.
//   FIFO: when selling, consume the batch expiring SOONEST first.
//
// MOVIMIENTO:
//   { id, type:"entrada"|"salida", productId, productName, batchId,
//     batchExpiry, qty, note, ts, saleId? }
//
// VENTA:
//   { id, ts, lines:[{productId, productName, barcode, qty, batches:[{batchId,expiry,qty}]}] }

// ═══════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════
const daysUntil = d => {
  const t=new Date(); t.setHours(0,0,0,0);
  const e=new Date(d); e.setHours(0,0,0,0);
  return Math.ceil((e-t)/86400000);
};
const statusOf = d => {
  if(d<=0)  return {key:"expired", color:T.red,    dim:T.redDim, badge:"VENCIDO", dot:"🔴", pri:0};
  if(d<=7)  return {key:"critical",color:T.red,    dim:T.redDim, badge:"CRÍTICO", dot:"🔴", pri:1};
  if(d<=15) return {key:"warning", color:T.yellow, dim:T.yelDim, badge:"ALERTA",  dot:"🟡", pri:2};
  return          {key:"ok",      color:T.accent, dim:T.accDim, badge:"OK",      dot:"🟢", pri:3};
};
const stockSt = qty => {
  if(qty<=0)  return {color:T.red,    dim:T.redDim,  label:"Sin stock",   dot:"🚫"};
  if(qty<=5)  return {color:T.yellow, dim:T.yelDim,  label:"Stock bajo",  dot:"⚠️"};
  if(qty<=15) return {color:T.blue,   dim:T.blueDim, label:"Stock medio", dot:"🔵"};
  return             {color:T.accent, dim:T.accDim,  label:"Stock OK",    dot:"🟢"};
};

const fmtDate = s => { if(!s)return"—"; const[y,m,d]=s.split("-"); return`${d}/${m}/${y}`; };
const fmtDT   = ts => {
  const d=new Date(ts);
  return d.toLocaleDateString("es-AR",{day:"2-digit",month:"2-digit"})+" "+
         d.toLocaleTimeString("es-AR",{hour:"2-digit",minute:"2-digit"});
};
const future  = n => { const d=new Date(); d.setDate(d.getDate()+n); return d.toISOString().split("T")[0]; };
const todayStr= () => new Date().toISOString().split("T")[0];
const uid     = () => Date.now().toString(36)+Math.random().toString(36).slice(2,8);
// Stronger non-cryptographic hash (FNV-1a 32-bit, salted) — good enough for local-only auth gating.
const hash = s => {
  const salted = "vcf_salt_"+s+"_v3";
  let h = 0x811c9dc5;
  for(let i=0;i<salted.length;i++){
    h ^= salted.charCodeAt(i);
    h = Math.imul(h, 0x01000193);
  }
  // Run twice with different seed mixing for extra spread
  let h2 = 0xdeadbeef ^ salted.length;
  for(let i=0;i<salted.length;i++){
    h2 = Math.imul(h2 ^ salted.charCodeAt(i), 2654435761);
    h2 ^= h2 >>> 15;
  }
  return (h>>>0).toString(36)+"-"+(h2>>>0).toString(36);
};

const CAT=["Lácteos","Panadería","Bebidas","Carnes","Verdulería","Limpieza",
           "Farmacia","Condimentos","Snacks","Congelados","Otros"];

// ── Per-user storage
const db = {
  get:(k,fb)=>{ try{const v=localStorage.getItem(k); return v!=null?JSON.parse(v):fb;}catch{return fb;} },
  set:(k,v)=>{ try{localStorage.setItem(k,JSON.stringify(v));}catch{} },
};
const USERS_KEY="vcf_users_v3";
const getUsers=()=>db.get(USERS_KEY,[]);
const saveUsers=u=>db.set(USERS_KEY,u);

// ── FIFO: given batches of a product, consume qty in order of:
// 1) earliest expiry date, 2) earliest createdAt (tiebreaker for same-date batches).
// This guarantees a deterministic, stable order every time — no ambiguity.
const sortFifo = batches => [...batches].sort((a,b)=>{
  const byExpiry = a.expiry.localeCompare(b.expiry);
  if(byExpiry!==0) return byExpiry;
  return (a.createdAt||0)-(b.createdAt||0);
});
const fifoConsume = (batches, qtyNeeded) => {
  const sorted = sortFifo(batches);
  const consumed = [];
  let remaining = qtyNeeded;
  const updated = sorted.map(b => {
    if(remaining <= 0) return b;
    const take = Math.min(b.qty, remaining);
    remaining -= take;
    if(take>0) consumed.push({batchId:b.id, expiry:b.expiry, qty:take});
    return {...b, qty: b.qty - take};
  }).filter(b => b.qty > 0);
  return { consumed, remaining, updated, ok: remaining === 0 };
};

// ── Aggregate stock for a product across all its batches
const productStock = (productId, batches) =>
  batches.filter(b=>b.productId===productId).reduce((a,b)=>a+b.qty, 0);

// ── Get batches for a product sorted FIFO (expiry asc, then createdAt asc)
const productBatches = (productId, batches) =>
  sortFifo(batches.filter(b=>b.productId===productId));

// ── Earliest expiry for a product
const earliestExpiry = (productId, batches) => {
  const pb = productBatches(productId, batches);
  return pb.length>0 ? pb[0].expiry : null;
};

// ═══════════════════════════════════════════════════════════════════
// GLOBAL CSS
// ═══════════════════════════════════════════════════════════════════
const CSS=`
  *,*::before,*::after{box-sizing:border-box;margin:0;padding:0;}
  html,body{height:100%;background:${T.bg};}
  body{color:${T.txt};font-family:'Inter','system-ui',sans-serif;font-size:14px;line-height:1.5;-webkit-font-smoothing:antialiased;}
  input,select,button,textarea{font-family:inherit;font-size:inherit;}
  input:focus,select:focus,textarea:focus{outline:none!important;border-color:${T.accent}!important;box-shadow:0 0 0 3px ${T.accGlow}!important;}
  button:focus-visible{outline:2px solid ${T.accent};outline-offset:2px;}
  ::-webkit-scrollbar{width:4px;height:4px;}
  ::-webkit-scrollbar-track{background:transparent;}
  ::-webkit-scrollbar-thumb{background:${T.bord2};border-radius:4px;}
  select option{background:${T.surf2};color:${T.txt};}
  @keyframes fadeUp {from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:none}}
  @keyframes fadeIn {from{opacity:0}to{opacity:1}}
  @keyframes slideR{from{opacity:0;transform:translateX(14px)}to{opacity:1;transform:none}}
  @keyframes scanPop{0%,100%{box-shadow:0 0 0 0 ${T.accent}30}60%{box-shadow:0 0 0 14px ${T.accent}00}}
  @keyframes blink{0%,100%{opacity:1}50%{opacity:.4}}
  .page{animation:fadeUp .2s ease both;}
  .nb:hover{background:${T.surf2}!important;color:${T.txt}!important;}
  .row:hover{background:${T.surf3}!important;}
  .delbtn:hover{background:${T.redDim}!important;border-color:${T.red}55!important;}
  .editbtn:hover{background:${T.blueDim}!important;border-color:${T.blue}55!important;}
  .sc{transition:transform .15s,box-shadow .15s;cursor:pointer;}
  .sc:hover{transform:translateY(-3px);box-shadow:0 10px 32px rgba(0,0,0,.4);}
  .sc:active{transform:translateY(-1px);}
  .qc{transition:transform .15s,box-shadow .15s;cursor:pointer;}
  .qc:hover{transform:translateY(-2px);box-shadow:0 8px 24px rgba(0,0,0,.35);}
  .tb:hover{background:${T.surf2}!important;}
  @media print{
    body *{visibility:hidden!important;}
    #pzone,#pzone *{visibility:visible!important;}
    #pzone{position:fixed!important;inset:0;background:#fff!important;color:#000!important;padding:32px 36px;font-family:Arial,sans-serif;font-size:12px;}
  }
`;

// ═══════════════════════════════════════════════════════════════════
// BASE UI
// ═══════════════════════════════════════════════════════════════════
const Inp=({sx={},fwd,...p})=><input ref={fwd} style={{background:T.bg,border:`1px solid ${T.border}`,borderRadius:9,padding:"10px 13px",color:T.txt,fontSize:13,width:"100%",transition:"border-color .15s,box-shadow .15s",...sx}} {...p}/>;
const Sel=({sx={},children,...p})=><select style={{background:T.bg,border:`1px solid ${T.border}`,borderRadius:9,padding:"10px 13px",color:p.value?T.txt:T.txtMuted,fontSize:13,width:"100%",cursor:"pointer",...sx}} {...p}>{children}</select>;
const Btn=({v="primary",sx={},children,disabled,...p})=>{
  const vs={primary:{background:T.accent,color:"#000",border:"none"},ghost:{background:"transparent",border:`1px solid ${T.border}`,color:T.txtSub},red:{background:T.redDim,border:`1px solid ${T.red}40`,color:T.red},blue:{background:T.blueDim,border:`1px solid ${T.blue}40`,color:T.blue},subtle:{background:T.surf2,border:`1px solid ${T.border}`,color:T.txtSub},purple:{background:T.purDim,border:`1px solid ${T.purple}40`,color:T.purple},orange:{background:T.oraDim,border:`1px solid ${T.orange}40`,color:T.orange}};
  return <button disabled={disabled} style={{border:"none",borderRadius:9,fontWeight:700,fontSize:13,cursor:disabled?"not-allowed":"pointer",display:"inline-flex",alignItems:"center",justifyContent:"center",gap:7,padding:"10px 18px",transition:"opacity .15s,filter .15s,transform .1s",opacity:disabled?0.45:1,pointerEvents:disabled?"none":"auto",...vs[v],...sx}} {...p}>{children}</button>;
};
const Lbl=({c,children})=><p style={{fontSize:10,fontWeight:800,color:c||T.txtMuted,textTransform:"uppercase",letterSpacing:"0.08em",marginBottom:6}}>{children}</p>;
const Hr=()=><div style={{height:1,background:T.border}}/>;
const Card=({sx={},children})=><div style={{background:T.surf,border:`1px solid ${T.border}`,borderRadius:14,overflow:"hidden",...sx}}>{children}</div>;
const CardHead=({title,sub,right})=>(
  <div style={{padding:"13px 18px",borderBottom:`1px solid ${T.border}`,display:"flex",alignItems:"center",justifyContent:"space-between",gap:12,flexWrap:"wrap"}}>
    <div><p style={{fontWeight:700,fontSize:13,color:T.txt}}>{title}</p>{sub&&<p style={{fontSize:11,color:T.txtSub,marginTop:2}}>{sub}</p>}</div>
    {right}
  </div>
);
const Chip=({color,dim,children})=><span style={{background:dim,color:color,border:`1px solid ${color}25`,borderRadius:20,padding:"2px 10px",fontSize:11,fontWeight:700,whiteSpace:"nowrap"}}>{children}</span>;
const Badge=({st})=><span style={{display:"inline-flex",alignItems:"center",gap:5,background:st.dim,color:st.color,border:`1px solid ${st.color}25`,borderRadius:6,padding:"3px 9px",fontSize:11,fontWeight:700,whiteSpace:"nowrap"}}>{st.dot} {st.badge}</span>;

// ── Toasts
function useToast(){
  const [list,setList]=useState([]);
  const push=useCallback((msg,type="ok")=>{
    const id=uid();
    setList(l=>[...l,{id,msg,type}]);
    setTimeout(()=>setList(l=>l.filter(t=>t.id!==id)),3500);
  },[]);
  return {list,push};
}
const Toasts=({list})=>{
  const bg=t=>t.type==="error"?T.red:t.type==="warn"?T.yellow:t.type==="purple"?T.purple:T.accent;
  return(
    <div style={{position:"fixed",bottom:24,right:24,zIndex:9999,display:"flex",flexDirection:"column",gap:8,pointerEvents:"none"}}>
      {list.map(t=><div key={t.id} style={{background:bg(t),color:"#000",padding:"10px 16px",borderRadius:10,fontWeight:700,fontSize:13,boxShadow:"0 6px 28px rgba(0,0,0,.55)",animation:"slideR .2s ease",maxWidth:360}}>{t.msg}</div>)}
    </div>
  );
};

// ── Modal
const Modal=({children,onClose,width=460})=>(
  <div style={{position:"fixed",inset:0,background:"rgba(0,0,0,.78)",zIndex:8888,display:"flex",alignItems:"center",justifyContent:"center",padding:"1rem",animation:"fadeIn .15s ease"}}
    onClick={e=>e.target===e.currentTarget&&onClose()}>
    <div style={{background:T.surf,border:`1px solid ${T.border}`,borderRadius:16,padding:"1.75rem",maxWidth:width,width:"100%",display:"flex",flexDirection:"column",gap:"1rem",maxHeight:"92vh",overflowY:"auto"}}>
      {children}
    </div>
  </div>
);
const MHead=({title,onClose})=><><div style={{display:"flex",justifyContent:"space-between",alignItems:"center"}}><p style={{fontWeight:900,fontSize:16,color:T.txt}}>{title}</p><button onClick={onClose} style={{background:"transparent",border:"none",color:T.txtSub,fontSize:22,cursor:"pointer",padding:"0 4px"}}>×</button></div><Hr/></>;
const Confirm=({msg,onOk,onCancel,label="Confirmar eliminación"})=>(
  <Modal onClose={onCancel} width={380}>
    <MHead title="Confirmar acción" onClose={onCancel}/>
    <p style={{color:T.txtSub,fontSize:13,lineHeight:1.6}}>{msg}</p>
    <div style={{display:"flex",gap:10,marginTop:4}}><Btn v="ghost" sx={{flex:1}} onClick={onCancel}>Cancelar</Btn><Btn v="red" sx={{flex:1}} onClick={onOk}>{label}</Btn></div>
  </Modal>
);

// ── Print zone
const PrintZone=({products,batches,storeName})=>{
  const now=new Date().toLocaleDateString("es-AR",{day:"2-digit",month:"2-digit",year:"numeric",hour:"2-digit",minute:"2-digit"});
  const rows=products.map(p=>{
    const pb=productBatches(p.id,batches);
    const qty=pb.reduce((a,b)=>a+b.qty,0);
    const exp=pb.length>0?pb[0].expiry:null;
    const days=exp?daysUntil(exp):999;
    return{...p,qty,expiry:exp,days,st:statusOf(days),batches:pb};
  }).filter(p=>p.days<=15&&p.qty>0).sort((a,b)=>a.days-b.days);
  return(
    <div id="pzone" style={{display:"none"}}>
      <div style={{borderBottom:"2px solid #111",paddingBottom:14,marginBottom:20,display:"flex",justifyContent:"space-between"}}>
        <div><h1 style={{fontSize:20,fontWeight:800}}>Vencify — Listado de Vencimientos</h1><p style={{fontSize:11,color:"#555",marginTop:3}}>{storeName} · {now}</p></div>
        <p style={{fontSize:11,color:"#888",alignSelf:"flex-end"}}>⚠️ Sistema FIFO — se muestra el lote más próximo a vencer</p>
      </div>
      {rows.length===0?<p style={{color:"green",fontWeight:700}}>✅ Sin productos próximos a vencer.</p>:
        <table style={{width:"100%",borderCollapse:"collapse",fontSize:11.5}}>
          <thead><tr style={{background:"#eee"}}>{["Estado","Producto","Código","Cat.","Lotes","Stock total","Próx. venc.","Días"].map(h=><th key={h} style={{padding:"7px 10px",border:"1px solid #ccc",textAlign:"left",fontWeight:800}}>{h}</th>)}</tr></thead>
          <tbody>{rows.map((p,i)=><tr key={p.id} style={{background:i%2?"#f7f7f7":"#fff"}}>
            <td style={{padding:"6px 10px",border:"1px solid #ddd",fontWeight:800,color:p.days<=7?"#b00":"#a06000"}}>{p.st.dot} {p.st.badge}</td>
            <td style={{padding:"6px 10px",border:"1px solid #ddd",fontWeight:600}}>{p.name}</td>
            <td style={{padding:"6px 10px",border:"1px solid #ddd",fontFamily:"monospace"}}>{p.barcode||"—"}</td>
            <td style={{padding:"6px 10px",border:"1px solid #ddd"}}>{p.category||"—"}</td>
            <td style={{padding:"6px 10px",border:"1px solid #ddd",textAlign:"center"}}>{p.batches.length}</td>
            <td style={{padding:"6px 10px",border:"1px solid #ddd",textAlign:"center",fontWeight:700}}>{p.qty}</td>
            <td style={{padding:"6px 10px",border:"1px solid #ddd",fontFamily:"monospace"}}>{fmtDate(p.expiry)}</td>
            <td style={{padding:"6px 10px",border:"1px solid #ddd",textAlign:"center",fontWeight:800,color:p.days<=7?"#b00":"#a06000"}}>{p.days<=0?"VENC":p.days}</td>
          </tr>)}</tbody>
        </table>
      }
      <p style={{marginTop:18,fontSize:10,color:"#aaa",borderTop:"1px solid #ddd",paddingTop:10}}>Vencify v6 · FIFO · {now}</p>
    </div>
  );
};

// ═══════════════════════════════════════════════════════════════════
// AUTH
// ═══════════════════════════════════════════════════════════════════
function AuthScreen({onLogin}){
  const [tab,setTab]=useState("login");
  const [f,setF]=useState({store:"",email:"",pass:"",pass2:""});
  const [err,setErr]=useState("");
  const [ok,setOk]=useState("");
  const ff=k=>e=>{setF(p=>({...p,[k]:e.target.value}));setErr("");};

  const doLogin=()=>{
    if(!f.email||!f.pass){setErr("Completá todos los campos.");return;}
    const u=getUsers().find(u=>u.email.toLowerCase()===f.email.toLowerCase());
    if(!u){setErr("No existe una cuenta con ese email.");return;}
    if(u.passHash!==hash(f.pass)){setErr("Contraseña incorrecta.");return;}
    onLogin(u);
  };
  const doReg=()=>{
    if(!f.store.trim()||!f.email.trim()||!f.pass||!f.pass2){setErr("Completá todos los campos.");return;}
    if(f.pass.length<4){setErr("Contraseña mínimo 4 caracteres.");return;}
    if(f.pass!==f.pass2){setErr("Las contraseñas no coinciden.");return;}
    const users=getUsers();
    if(users.find(u=>u.email.toLowerCase()===f.email.toLowerCase())){setErr("Ya existe una cuenta con ese email.");return;}
    const nu={id:uid(),store:f.store.trim(),email:f.email.trim().toLowerCase(),passHash:hash(f.pass),createdAt:Date.now()};
    saveUsers([...users,nu]);
    setOk("¡Cuenta creada! Iniciá sesión.");
    setTab("login");setF(p=>({...p,store:"",pass:"",pass2:""}));
  };
  const Tab=({id,l})=><button onClick={()=>{setTab(id);setErr("");}} style={{flex:1,padding:"10px",background:tab===id?T.accent:"transparent",color:tab===id?"#000":T.txtSub,border:"none",borderRadius:8,fontWeight:700,fontSize:13,cursor:"pointer",transition:"all .15s"}}>{l}</button>;

  return(
    <div style={{minHeight:"100vh",background:T.bg,display:"flex",alignItems:"center",justifyContent:"center",padding:"1.5rem"}}>
      <style>{CSS}</style>
      <div style={{width:"100%",maxWidth:380,display:"flex",flexDirection:"column",gap:"1.5rem"}}>
        <div style={{textAlign:"center"}}>
          <div style={{display:"inline-flex",alignItems:"center",gap:14,marginBottom:10}}>
            <div style={{width:48,height:48,borderRadius:14,background:`linear-gradient(135deg,${T.accent},#00B388)`,display:"flex",alignItems:"center",justifyContent:"center",fontWeight:900,fontSize:24,color:"#000",boxShadow:`0 0 0 6px ${T.accGlow}, 0 4px 16px ${T.accent}25`}}>V</div>
            <span style={{fontSize:32,fontWeight:900,color:T.txt,letterSpacing:"-1.5px"}}>Vencify</span>
          </div>
          <p style={{color:T.txtSub,fontSize:14}}>Control de vencimientos y stock para comercios</p>
        </div>
        <Card sx={{padding:"1.75rem",display:"flex",flexDirection:"column",gap:"1rem",boxShadow:"0 12px 40px rgba(0,0,0,.35)"}}>
          <div style={{display:"flex",gap:4,background:T.surf2,borderRadius:10,padding:4}}>
            <Tab id="login" l="Iniciar sesión"/><Tab id="register" l="Crear cuenta"/>
          </div>
          {ok&&<div style={{background:T.accDim,border:`1px solid ${T.accent}30`,borderRadius:9,padding:"10px 13px",color:T.accent,fontSize:12,fontWeight:600}}>{ok}</div>}
          {tab==="login"&&<>
            <div><Lbl>Email</Lbl><Inp type="email" placeholder="tu@email.com" value={f.email} onChange={ff("email")} onKeyDown={e=>e.key==="Enter"&&doLogin()} autoFocus/></div>
            <div><Lbl>Contraseña</Lbl><Inp type="password" placeholder="Tu contraseña" value={f.pass} onChange={ff("pass")} onKeyDown={e=>e.key==="Enter"&&doLogin()}/></div>
            {err&&<p style={{color:T.red,fontSize:12,fontWeight:600}}>{err}</p>}
            <Btn sx={{width:"100%",padding:"12px",fontSize:14,marginTop:4}} onClick={doLogin}>Entrar al sistema</Btn>
          </>}
          {tab==="register"&&<>
            <div><Lbl>Nombre del comercio</Lbl><Inp placeholder="Ej: Supermercado Don José" value={f.store} onChange={ff("store")} autoFocus/></div>
            <div><Lbl>Email</Lbl><Inp type="email" placeholder="tu@email.com" value={f.email} onChange={ff("email")}/></div>
            <div><Lbl>Contraseña</Lbl><Inp type="password" placeholder="Mínimo 4 caracteres" value={f.pass} onChange={ff("pass")}/></div>
            <div><Lbl>Repetir contraseña</Lbl><Inp type="password" placeholder="Repetí" value={f.pass2} onChange={ff("pass2")} onKeyDown={e=>e.key==="Enter"&&doReg()}/></div>
            {err&&<p style={{color:T.red,fontSize:12,fontWeight:600}}>{err}</p>}
            <Btn sx={{width:"100%",padding:"12px",fontSize:14,marginTop:4}} onClick={doReg}>Crear mi cuenta</Btn>
            <p style={{color:T.txtMuted,fontSize:11,textAlign:"center",lineHeight:1.5}}>🔒 Tus datos quedan guardados solo en esta PC, no se suben a internet.</p>
          </>}
        </Card>
      </div>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════
// BATCH DETAIL MODAL — shows all batches (lotes) for a product
// ═══════════════════════════════════════════════════════════════════
function BatchModal({product,batches,onAddBatch,onRemoveBatch,onClose}){
  const [expiry,setExpiry]=useState("");
  const [qty,setQty]=useState("");
  const pb=productBatches(product.id,batches);
  const total=pb.reduce((a,b)=>a+b.qty,0);

  const add=()=>{
    const q=parseInt(qty,10);
    if(!expiry||!Number.isFinite(q)||q<=0)return;
    onAddBatch({id:uid(),productId:product.id,expiry,qty:q,createdAt:Date.now()});
    setExpiry("");setQty("");
  };

  return(
    <Modal onClose={onClose} width={520}>
      <MHead title={`Lotes — ${product.name}`} onClose={onClose}/>

      {/* Summary */}
      <div style={{background:T.surf2,border:`1px solid ${T.border}`,borderRadius:10,padding:"12px 16px",display:"flex",justifyContent:"space-between",alignItems:"center"}}>
        <div>
          <Lbl>Stock total</Lbl>
          <p style={{fontSize:28,fontWeight:900,color:stockSt(total).color,fontFamily:T.mono,letterSpacing:"-1px"}}>{total}</p>
        </div>
        <div style={{textAlign:"right"}}>
          <Lbl>Lotes activos</Lbl>
          <p style={{fontSize:28,fontWeight:900,color:T.txt,fontFamily:T.mono}}>{pb.length}</p>
        </div>
      </div>

      {/* FIFO info */}
      <div style={{background:T.accDim,border:`1px solid ${T.accent}28`,borderRadius:9,padding:"10px 14px",display:"flex",gap:10}}>
        <span style={{flexShrink:0}}>ℹ️</span>
        <p style={{fontSize:12,color:T.txt,lineHeight:1.6}}>
          <strong style={{color:T.accent}}>Sistema FIFO activo.</strong> Al vender, se descuenta primero el lote con vencimiento más próximo. Los lotes se muestran en orden de consumo.
        </p>
      </div>

      {/* Batches list */}
      {pb.length===0
        ?<div style={{padding:"1.5rem",textAlign:"center",color:T.txtSub,fontSize:13}}>Sin lotes registrados.</div>
        :<div style={{display:"flex",flexDirection:"column",gap:8}}>
          {pb.map((b,i)=>{
            const days=daysUntil(b.expiry);
            const st=statusOf(days);
            return(
              <div key={b.id} style={{background:i===0?st.dim:T.surf2,border:`1px solid ${i===0?st.color+"45":T.border}`,borderRadius:10,padding:"12px 14px",display:"flex",alignItems:"center",justifyContent:"space-between",gap:12,boxShadow:i===0?`0 0 0 1px ${st.color}15, 0 4px 16px ${st.color}10`:"none"}}>
                <div style={{display:"flex",alignItems:"center",gap:12}}>
                  <div style={{textAlign:"center",minWidth:36}}>
                    <p style={{fontSize:10,color:T.txtMuted,fontWeight:700,textTransform:"uppercase"}}>#{i+1}</p>
                    {i===0&&<p style={{fontSize:9,color:st.color,fontWeight:800,textTransform:"uppercase",marginTop:2}}>FIFO</p>}
                  </div>
                  <div>
                    <div style={{display:"flex",alignItems:"center",gap:8}}>
                      <Badge st={st}/>
                      <span style={{fontFamily:T.mono,fontSize:13,color:T.txt,fontWeight:700}}>{fmtDate(b.expiry)}</span>
                    </div>
                    <p style={{fontSize:11,color:T.txtSub,marginTop:3}}>
                      {days<=0?"Ya vencido":days===1?"Vence mañana":`Vence en ${days} días`} · Ingresado {fmtDate(new Date(b.createdAt).toISOString().split("T")[0])}
                    </p>
                  </div>
                </div>
                <div style={{display:"flex",alignItems:"center",gap:10,flexShrink:0}}>
                  <div style={{textAlign:"right"}}>
                    <p style={{fontFamily:T.mono,fontWeight:900,fontSize:22,color:i===0?st.color:T.txt,letterSpacing:"-1px"}}>{b.qty}</p>
                    <p style={{fontSize:10,color:T.txtMuted}}>unidades</p>
                  </div>
                  <button className="delbtn" onClick={()=>onRemoveBatch(b.id)} style={{background:"transparent",border:`1px solid ${T.red}35`,color:T.red,borderRadius:7,padding:"5px 9px",fontSize:12,cursor:"pointer",transition:"all .15s"}}>✕</button>
                </div>
              </div>
            );
          })}
        </div>
      }

      <Hr/>

      {/* Add new batch */}
      <div>
        <Lbl c={T.accent}>Agregar nuevo lote</Lbl>
        <div style={{display:"grid",gridTemplateColumns:"1fr 100px auto",gap:"0.75rem",alignItems:"flex-end"}}>
          <div>
            <p style={{fontSize:11,color:T.txtSub,marginBottom:5,fontWeight:600}}>Fecha de vencimiento</p>
            <Inp type="date" min={todayStr()} value={expiry} onChange={e=>setExpiry(e.target.value)}/>
          </div>
          <div>
            <p style={{fontSize:11,color:T.txtSub,marginBottom:5,fontWeight:600}}>Cantidad</p>
            <Inp type="number" min="1" step="1" sx={{fontFamily:T.mono,textAlign:"center",fontWeight:700}} placeholder="0" value={qty} onChange={e=>setQty(e.target.value)} onKeyDown={e=>e.key==="Enter"&&add()}/>
          </div>
          <Btn onClick={add} sx={{padding:"10px 16px"}} disabled={!expiry||!qty||parseInt(qty)<=0}>+ Agregar</Btn>
        </div>
        {expiry&&<p style={{fontSize:11,color:T.txtSub,marginTop:6}}>
          {daysUntil(expiry)<=0?"⚠️ Esta fecha ya está vencida":
           daysUntil(expiry)<=7?`🔴 Vence en ${daysUntil(expiry)} días`:
           daysUntil(expiry)<=15?`🟡 Vence en ${daysUntil(expiry)} días`:
           `🟢 Vence en ${daysUntil(expiry)} días`}
        </p>}
      </div>
    </Modal>
  );
}

// ═══════════════════════════════════════════════════════════════════
// EDIT PRODUCT MODAL
// ═══════════════════════════════════════════════════════════════════
function EditModal({product,onSave,onClose}){
  const [f,setF]=useState({...product});
  const ff=k=>e=>setF(p=>({...p,[k]:e.target.value}));
  return(
    <Modal onClose={onClose}>
      <MHead title="Editar producto" onClose={onClose}/>
      <div><Lbl>Nombre *</Lbl><Inp value={f.name} onChange={ff("name")} autoFocus/></div>
      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:"0.75rem"}}>
        <div><Lbl>Código de barras</Lbl><Inp sx={{fontFamily:T.mono}} value={f.barcode} onChange={ff("barcode")}/></div>
        <div><Lbl>Categoría</Lbl>
          <Sel value={f.category} onChange={ff("category")}>
            <option value="">Sin categoría</option>
            {CAT.map(c=><option key={c}>{c}</option>)}
          </Sel>
        </div>
      </div>
      <div><Lbl>Stock mínimo (alerta)</Lbl><Inp type="number" min="0" step="1" sx={{fontFamily:T.mono}} value={f.minStock||5} onChange={ff("minStock")} placeholder="5"/></div>
      <Hr/>
      <div style={{display:"flex",gap:10}}>
        <Btn v="ghost" sx={{flex:1}} onClick={onClose}>Cancelar</Btn>
        <Btn sx={{flex:1}} onClick={()=>{if(!f.name.trim())return;onSave({...f,minStock:parseInt(f.minStock)||5,name:f.name.trim()});}}>Guardar cambios</Btn>
      </div>
    </Modal>
  );
}

// ═══════════════════════════════════════════════════════════════════
// PAGE: DASHBOARD
// ═══════════════════════════════════════════════════════════════════
function Dashboard({products,batches,movements,counts,setPage,onPrint,user}){
  const urgent=products.map(p=>{
    const exp=earliestExpiry(p.id,batches);
    const qty=productStock(p.id,batches);
    const days=exp?daysUntil(exp):999;
    return{...p,exp,qty,days,st:statusOf(days)};
  }).filter(p=>p.days<=7&&p.qty>0).sort((a,b)=>a.days-b.days).slice(0,6);

  const recentMov=movements.slice().sort((a,b)=>b.ts-a.ts).slice(0,5);

  const buckets=[
    {l:"Vencidos",ct:counts.expired,  c:T.red},
    {l:"1-7d",    ct:counts.critical, c:T.red},
    {l:"8-15d",   ct:counts.warning,  c:T.yellow},
    {l:"+15d",    ct:counts.ok,       c:T.accent},
  ];
  const maxB=Math.max(...buckets.map(b=>b.ct),1);
  const hour=new Date().getHours();

  return(
    <div className="page">
      <div style={{marginBottom:24}}>
        <p style={{color:T.txtSub,fontSize:13,marginBottom:4}}>{new Date().toLocaleDateString("es-AR",{weekday:"long",day:"numeric",month:"long"})}</p>
        <h1 style={{fontSize:24,fontWeight:900,letterSpacing:"-0.5px"}}>
          {hour<12?"Buenos días":"Buenas tardes"}, <span style={{color:T.accent}}>{user.store}</span> 👋
        </h1>
      </div>

      <div style={{display:"grid",gridTemplateColumns:"repeat(4,1fr)",gap:12,marginBottom:14}}>
        {[
          {l:"Productos",  v:counts.all,      c:T.accent, d:T.accDim, i:"📦",pg:"list"},
          {l:"Vencidos",   v:counts.expired,  c:T.red,    d:T.redDim, i:"💀",pg:"list"},
          {l:"Críticos",   v:counts.critical, c:T.red,    d:T.redDim, i:"🔴",pg:"list"},
          {l:"Sin stock",  v:counts.noStock,  c:T.yellow, d:T.yelDim, i:"📭",pg:"stock"},
        ].map(s=>(
          <button key={s.l} className="sc" onClick={()=>setPage(s.pg)}
            style={{background:s.d,border:`1px solid ${s.c}18`,borderRadius:14,padding:"18px 16px",textAlign:"left",display:"flex",flexDirection:"column",gap:6}}>
            <span style={{fontSize:22}}>{s.i}</span>
            <span style={{fontSize:36,fontWeight:900,color:s.c,letterSpacing:"-2px",lineHeight:1}}>{s.v}</span>
            <span style={{fontSize:11,color:T.txtSub,fontWeight:700,textTransform:"uppercase",letterSpacing:"0.05em"}}>{s.l}</span>
          </button>
        ))}
      </div>

      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:12,marginBottom:14}}>
        <Card sx={{padding:"1.25rem"}}>
          <Lbl>Distribución de vencimientos</Lbl>
          <div style={{display:"flex",alignItems:"flex-end",gap:10,height:72,marginTop:12}}>
            {buckets.map(b=>(
              <div key={b.l} style={{flex:1,display:"flex",flexDirection:"column",alignItems:"center",gap:5}}>
                <span style={{fontSize:11,fontWeight:800,color:b.ct>0?b.c:T.txtMuted}}>{b.ct}</span>
                <div style={{width:"100%",background:b.ct>0?b.c:T.bord2,height:`${Math.max((b.ct/maxB)*52,b.ct>0?4:2)}px`,borderRadius:"4px 4px 0 0",transition:"height .4s ease"}}/>
                <span style={{fontSize:9,color:T.txtSub,fontWeight:700,textAlign:"center"}}>{b.l}</span>
              </div>
            ))}
          </div>
        </Card>
        <div style={{display:"flex",flexDirection:"column",gap:10}}>
          <button className="qc" onClick={()=>setPage("scan")} style={{flex:1,background:`linear-gradient(135deg,${T.accent}14,${T.accent}06)`,border:`1px solid ${T.accent}28`,borderRadius:12,padding:"14px 16px",textAlign:"left",display:"flex",alignItems:"center",gap:12}}>
            <span style={{fontSize:26}}>📷</span><div><p style={{fontWeight:800,fontSize:14,color:T.txt}}>Escanear</p><p style={{fontSize:11,color:T.txtSub,marginTop:1}}>Scanner USB · F2</p></div>
          </button>
          <button className="qc" onClick={()=>setPage("caja")} style={{flex:1,background:`linear-gradient(135deg,${T.orange}14,${T.orange}06)`,border:`1px solid ${T.orange}28`,borderRadius:12,padding:"14px 16px",textAlign:"left",display:"flex",alignItems:"center",gap:12}}>
            <span style={{fontSize:26}}>🛒</span><div><p style={{fontWeight:800,fontSize:14,color:T.txt}}>Modo caja</p><p style={{fontSize:11,color:T.txtSub,marginTop:1}}>Descuento automático FIFO</p></div>
          </button>
          <button className="qc" onClick={onPrint} style={{flex:1,background:T.surf,border:`1px solid ${T.border}`,borderRadius:12,padding:"14px 16px",textAlign:"left",display:"flex",alignItems:"center",gap:12}}>
            <span style={{fontSize:26}}>🖨️</span><div><p style={{fontWeight:800,fontSize:14,color:T.txt}}>Imprimir</p><p style={{fontSize:11,color:T.txtSub,marginTop:1}}>Listado de vencimientos</p></div>
          </button>
        </div>
      </div>

      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:12}}>
        <Card>
          <CardHead title={urgent.length>0?"⚠️ Urgentes":"✅ Sin urgentes"} sub={urgent.length>0?"Vence el lote más próximo en ≤7 días":undefined} right={urgent.length>0&&<Chip color={T.red} dim={T.redDim}>{urgent.length}</Chip>}/>
          {urgent.length===0?<div style={{padding:"1.5rem",textAlign:"center",color:T.txtSub,fontSize:13}}>🎉 Todo en orden</div>
            :urgent.map((p,i)=>(
              <div key={p.id} className="row" style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"10px 16px",borderBottom:i<urgent.length-1?`1px solid ${T.border}`:"none",transition:"background .1s"}}>
                <div style={{minWidth:0}}>
                  <p style={{fontWeight:600,fontSize:12,whiteSpace:"nowrap",overflow:"hidden",textOverflow:"ellipsis"}}>{p.name}</p>
                  <p style={{fontSize:10,color:T.txtSub,marginTop:1}}>{p.category||"—"} · Stock: {p.qty}</p>
                </div>
                <div style={{textAlign:"right",flexShrink:0,marginLeft:10}}>
                  <p style={{fontWeight:900,color:p.st.color,fontSize:13,fontFamily:T.mono}}>{p.days<=0?"VENC":p.days+"d"}</p>
                  <p style={{fontSize:10,color:T.txtSub,fontFamily:T.mono}}>{fmtDate(p.exp)}</p>
                </div>
              </div>
            ))
          }
        </Card>
        <Card>
          <CardHead title="📋 Últimos movimientos"/>
          {recentMov.length===0?<div style={{padding:"1.5rem",textAlign:"center",color:T.txtSub,fontSize:13}}>Sin movimientos aún</div>
            :recentMov.map((m,i)=>(
              <div key={m.id} className="row" style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"10px 16px",borderBottom:i<recentMov.length-1?`1px solid ${T.border}`:"none",transition:"background .1s"}}>
                <div style={{display:"flex",alignItems:"center",gap:10,minWidth:0}}>
                  <span style={{fontSize:14,flexShrink:0}}>{m.type==="entrada"?"📥":"📤"}</span>
                  <div style={{minWidth:0}}>
                    <p style={{fontWeight:600,fontSize:12,whiteSpace:"nowrap",overflow:"hidden",textOverflow:"ellipsis"}}>{m.productName}</p>
                    <p style={{fontSize:10,color:T.txtSub}}>{fmtDT(m.ts)}{m.note&&` · ${m.note}`}</p>
                  </div>
                </div>
                <span style={{fontWeight:900,color:m.type==="entrada"?T.accent:T.red,fontSize:13,fontFamily:T.mono,flexShrink:0,marginLeft:8}}>{m.type==="entrada"?"+":"-"}{m.qty}</span>
              </div>
            ))
          }
        </Card>
      </div>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════
// PAGE: SCAN (add product + first batch)
// ═══════════════════════════════════════════════════════════════════
function ScanPage({products,batches,setProducts,setBatches,addMovement,push}){
  const [step,setStep]=useState("barcode");
  const [raw,setRaw]=useState("");
  const [form,setForm]=useState({name:"",barcode:"",category:"",expiry:"",qty:"1",minStock:"5"});
  const [matchedProduct,setMatchedProduct]=useState(null); // existing product found by barcode
  const [anim,setAnim]=useState(false);
  const [count,setCount]=useState(0);
  const bRef=useRef(null);
  const nRef=useRef(null);
  useEffect(()=>{ if(step==="barcode")setTimeout(()=>bRef.current?.focus(),80); },[step]);

  const onBarcode=e=>{
    if(e.key!=="Enter"||!raw.trim())return;
    setAnim(true); setTimeout(()=>setAnim(false),600);
    const code=raw.trim();
    const existing=products.find(p=>p.barcode===code);
    if(existing){
      push(`"${existing.name}" ya registrado — agregando nuevo lote.`,"warn");
      setMatchedProduct(existing);
      setForm(f=>({...f,barcode:code,name:existing.name,category:existing.category||"",minStock:String(existing.minStock||5),qty:"1"}));
    } else {
      setMatchedProduct(null);
      setForm(f=>({...f,barcode:code,name:"",category:"",qty:"1",minStock:"5"}));
    }
    setStep("details");
    setTimeout(()=>nRef.current?.focus(),100);
  };

  const save=()=>{
    if(!form.name.trim()||!form.expiry){push("Completá nombre y fecha de vencimiento.","error");return;}
    const qty=Math.max(1,parseInt(form.qty)||1);
    const minStock=parseInt(form.minStock)||5;
    let productId;

    if(matchedProduct){
      // Update existing product metadata if changed
      productId=matchedProduct.id;
      setProducts(prev=>prev.map(p=>p.id===productId?{...p,name:form.name.trim(),category:form.category,minStock}:p));
    } else {
      // Create new product catalog entry
      const np={id:uid(),barcode:form.barcode.trim(),name:form.name.trim(),category:form.category,minStock,createdAt:Date.now()};
      productId=np.id;
      setProducts(prev=>[np,...prev]);
    }

    // Always create a new batch
    const batch={id:uid(),productId,expiry:form.expiry,qty,createdAt:Date.now()};
    setBatches(prev=>[...prev,batch]);
    addMovement({id:uid(),type:"entrada",qty,productId,productName:form.name.trim(),batchId:batch.id,batchExpiry:form.expiry,note:"Alta de lote",ts:Date.now()});
    push(`✓ Lote de "${form.name.trim()}" registrado — vence ${fmtDate(form.expiry)}.`);
    setCount(c=>c+1);
    setRaw("");setForm({name:"",barcode:"",category:"",expiry:"",qty:"1",minStock:"5"});setMatchedProduct(null);setStep("barcode");
  };

  const pD=form.expiry?daysUntil(form.expiry):null;
  const pSt=pD!==null?statusOf(pD):null;
  const ff=k=>e=>setForm(f=>({...f,[k]:e.target.value}));

  return(
    <div className="page" style={{maxWidth:560,margin:"0 auto"}}>
      <div style={{marginBottom:24,display:"flex",alignItems:"flex-start",justifyContent:"space-between"}}>
        <div><h1 style={{fontSize:22,fontWeight:900,letterSpacing:"-0.5px"}}>Escanear producto</h1>
          <p style={{color:T.txtSub,fontSize:13,marginTop:4}}>Cada escaneo crea un nuevo lote con su fecha de vencimiento</p></div>
        {count>0&&<Chip color={T.accent} dim={T.accDim}>{count} lote{count!==1?"s":""} registrado{count!==1?"s":""}</Chip>}
      </div>

      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:10,marginBottom:20}}>
        {["Escanear código","Datos del lote"].map((s,i)=>{
          const active=(i===0&&step==="barcode")||(i===1&&step==="details");
          const done=i===0&&step==="details";
          return(
            <div key={s} style={{padding:"10px 14px",borderRadius:10,background:active?T.accDim:done?"#00D4A008":T.surf2,border:`1px solid ${active?T.accent+"44":done?T.accent+"22":T.border}`,display:"flex",alignItems:"center",gap:10}}>
              <div style={{width:22,height:22,borderRadius:"50%",flexShrink:0,display:"flex",alignItems:"center",justifyContent:"center",fontSize:11,fontWeight:900,background:active?T.accent:done?T.accent+"33":T.surf,color:active?"#000":done?T.accent:T.txtMuted}}>{done?"✓":i+1}</div>
              <span style={{fontSize:12,fontWeight:700,color:active?T.accent:done?T.accent+"88":T.txtSub}}>{s}</span>
            </div>
          );
        })}
      </div>

      {step==="barcode"&&(
        <Card sx={{padding:"2rem",display:"flex",flexDirection:"column",gap:"1.5rem",alignItems:"center",border:`2px solid ${anim?T.accent:T.border}`,transition:"border-color .3s",animation:anim?"scanPop .7s ease":undefined}}>
          <div style={{textAlign:"center"}}>
            <div style={{fontSize:52,marginBottom:10}}>🔎</div>
            <p style={{fontWeight:700,fontSize:15,marginBottom:6}}>Scanner listo</p>
            <p style={{color:T.txtSub,fontSize:13,lineHeight:1.6}}>Hacé click en el campo y apretá el gatillo</p>
          </div>
          <div style={{width:"100%"}}>
            <Lbl>Código de barras</Lbl>
            <input ref={bRef} style={{background:T.bg,border:`2px solid ${T.accent}`,borderRadius:10,padding:"14px 18px",color:T.txt,fontSize:20,width:"100%",fontFamily:T.mono,letterSpacing:"3px",textAlign:"center",boxShadow:`0 0 0 4px ${T.accGlow}`,animation:"blink 2.5s ease infinite"}}
              placeholder="▌ Esperando scanner..." value={raw} onChange={e=>setRaw(e.target.value)} onKeyDown={onBarcode}/>
          </div>
          <Btn v="subtle" sx={{width:"100%",fontSize:12}} onClick={()=>{setMatchedProduct(null);setForm(f=>({...f,barcode:raw}));setStep("details");setTimeout(()=>nRef.current?.focus(),100);}}>Ingresar manualmente →</Btn>
          <p style={{color:T.txtMuted,fontSize:11,textAlign:"center"}}>Atajo: <kbd style={{background:T.surf2,border:`1px solid ${T.border}`,borderRadius:4,padding:"1px 6px",fontFamily:T.mono,fontSize:10}}>F2</kbd></p>
        </Card>
      )}

      {step==="details"&&(
        <Card sx={{padding:"1.5rem",display:"flex",flexDirection:"column",gap:"1rem"}}>
          <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",paddingBottom:"0.875rem",borderBottom:`1px solid ${T.border}`}}>
            <div>
              <Lbl>Código escaneado</Lbl>
              <p style={{fontFamily:T.mono,color:T.accent,fontWeight:700,fontSize:17}}>{form.barcode||"(manual)"}</p>
            </div>
            <Btn v="ghost" sx={{fontSize:12,padding:"7px 12px"}} onClick={()=>{setStep("barcode");setRaw("");}}>← Volver</Btn>
          </div>

          {matchedProduct&&(
            <div style={{background:T.accDim,border:`1px solid ${T.accent}28`,borderRadius:9,padding:"10px 14px",display:"flex",gap:10,alignItems:"center"}}>
              <span>✓</span>
              <p style={{fontSize:12,color:T.txt}}>Producto existente encontrado. Se creará un <strong style={{color:T.accent}}>nuevo lote</strong> para este producto.</p>
            </div>
          )}

          <div><Lbl>Nombre del producto *</Lbl><Inp fwd={nRef} placeholder="Ej: Mayonesa Hellmann's 500g" value={form.name} onChange={ff("name")}/></div>
          <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:"0.75rem"}}>
            <div><Lbl>Categoría</Lbl>
              <Sel value={form.category} onChange={ff("category")}><option value="">Sin categoría</option>{CAT.map(c=><option key={c}>{c}</option>)}</Sel>
            </div>
            <div><Lbl>Stock mínimo</Lbl><Inp type="number" min="0" step="1" sx={{fontFamily:T.mono}} value={form.minStock} onChange={ff("minStock")}/></div>
          </div>
          <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:"0.75rem"}}>
            <div><Lbl>Fecha de vencimiento *</Lbl><Inp type="date" value={form.expiry} onChange={ff("expiry")} onKeyDown={e=>e.key==="Enter"&&save()}/></div>
            <div><Lbl>Cantidad en este lote</Lbl><Inp type="number" min="1" step="1" sx={{fontFamily:T.mono}} value={form.qty} onChange={ff("qty")}/></div>
          </div>
          {pSt&&(
            <div style={{background:pSt.dim,border:`1px solid ${pSt.color}25`,borderRadius:9,padding:"10px 14px",display:"flex",alignItems:"center",gap:10}}>
              <span>{pSt.dot}</span>
              <span style={{color:pSt.color,fontWeight:700,fontSize:13}}>{pD<=0?"Ya vencido":pD<=7?`Crítico — ${pD}d`:pD<=15?`Alerta — ${pD}d`:`OK — ${pD}d`}</span>
            </div>
          )}
          <Btn sx={{width:"100%",padding:"12px",fontSize:14,marginTop:4}} onClick={save}>✓ Registrar lote y escanear siguiente</Btn>
        </Card>
      )}
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════
// PAGE: PRODUCTS LIST
// ═══════════════════════════════════════════════════════════════════
function ListPage({products,batches,setProducts,setBatches,addMovement,push}){
  const [filter,setFilter]=useState("all");
  const [search,setSearch]=useState("");
  const [sortCol,setSortCol]=useState("days");
  const [sortAsc,setSortAsc]=useState(true);
  const [editP,setEditP]=useState(null);
  const [batchP,setBatchP]=useState(null);
  const [confirmId,setConfirmId]=useState(null);

  const enriched=products.map(p=>{
    const pb=productBatches(p.id,batches);
    const qty=pb.reduce((a,b)=>a+b.qty,0);
    const exp=pb.length>0?pb[0].expiry:null;
    const days=exp?daysUntil(exp):999;
    return{...p,qty,exp,days,batchCount:pb.length,st:statusOf(days),ss:stockSt(qty)};
  }).filter(p=>{
    if(filter==="critical") return p.days<=7&&p.qty>0;
    if(filter==="warning")  return p.days>7&&p.days<=15&&p.qty>0;
    if(filter==="ok")       return p.days>15&&p.qty>0;
    if(filter==="nostock")  return p.qty===0;
    return true;
  }).filter(p=>{
    const q=search.toLowerCase();
    return !q||p.name.toLowerCase().includes(q)||(p.barcode||"").includes(q)||(p.category||"").toLowerCase().includes(q);
  }).sort((a,b)=>{
    let av=sortCol==="days"?a.days:sortCol==="qty"?a.qty:a[sortCol];
    let bv=sortCol==="days"?b.days:sortCol==="qty"?b.qty:b[sortCol];
    if(typeof av==="string") av=av.toLowerCase();
    if(typeof bv==="string") bv=bv.toLowerCase();
    return sortAsc?(av>bv?1:-1):(av<bv?1:-1);
  });

  const cts={
    all:products.length,
    critical:products.filter(p=>{ const exp=earliestExpiry(p.id,batches);return exp&&daysUntil(exp)<=7&&productStock(p.id,batches)>0; }).length,
    warning:products.filter(p=>{ const exp=earliestExpiry(p.id,batches);const d=exp?daysUntil(exp):999;return d>7&&d<=15&&productStock(p.id,batches)>0; }).length,
    ok:products.filter(p=>{ const exp=earliestExpiry(p.id,batches);const d=exp?daysUntil(exp):999;return d>15&&productStock(p.id,batches)>0; }).length,
    nostock:products.filter(p=>productStock(p.id,batches)===0).length,
  };

  const TH=({col,label,align="left"})=>(
    <th onClick={()=>col&&(sortCol===col?setSortAsc(a=>!a):(setSortCol(col),setSortAsc(true)))} style={{padding:"10px 12px",textAlign:align,fontSize:10,fontWeight:800,color:sortCol===col?T.accent:T.txtMuted,textTransform:"uppercase",letterSpacing:"0.07em",borderBottom:`1px solid ${T.border}`,background:T.bg,cursor:col?"pointer":"default",userSelect:"none",whiteSpace:"nowrap"}}>
      {label}{col&&sortCol===col?(sortAsc?" ↑":" ↓"):""}
    </th>
  );

  return(
    <div className="page">
      {editP&&<EditModal product={editP} onSave={u=>{setProducts(p=>p.map(x=>x.id===u.id?u:x));push(`"${u.name}" actualizado.`);setEditP(null);}} onClose={()=>setEditP(null)}/>}
      {batchP&&<BatchModal product={batchP} batches={batches}
        onAddBatch={b=>{
          setBatches(prev=>[...prev,b]);
          addMovement({id:uid(),type:"entrada",qty:b.qty,productId:batchP.id,productName:batchP.name,batchId:b.id,batchExpiry:b.expiry,note:"Lote manual",ts:Date.now()});
          push(`✓ Lote registrado — ${b.qty} unidades vencen ${fmtDate(b.expiry)}.`);
        }}
        onRemoveBatch={bid=>{
          const b=batches.find(x=>x.id===bid);
          setBatches(prev=>prev.filter(x=>x.id!==bid));
          push(`Lote de ${fmtDate(b?.expiry)} eliminado.`,"warn");
        }}
        onClose={()=>setBatchP(null)}/>}
      {confirmId&&<Confirm
        msg={`¿Eliminar "${products.find(p=>p.id===confirmId)?.name}" y todos sus lotes? Esta acción no se puede deshacer.`}
        onOk={()=>{
          const p=products.find(x=>x.id===confirmId);
          setProducts(prev=>prev.filter(x=>x.id!==confirmId));
          setBatches(prev=>prev.filter(b=>b.productId!==confirmId));
          push(`"${p?.name}" eliminado.`,"warn");
          setConfirmId(null);
        }}
        onCancel={()=>setConfirmId(null)}/>}

      <div style={{marginBottom:20}}>
        <h1 style={{fontSize:22,fontWeight:900,letterSpacing:"-0.5px"}}>Productos</h1>
        <p style={{color:T.txtSub,fontSize:13,marginTop:4}}>{products.length} productos · sistema FIFO activo</p>
      </div>

      <div style={{display:"flex",gap:8,flexWrap:"wrap",alignItems:"center",marginBottom:14}}>
        {[{k:"all",l:`Todos (${cts.all})`},{k:"critical",l:`🔴 Críticos (${cts.critical})`},{k:"warning",l:`🟡 Alertas (${cts.warning})`},{k:"ok",l:`🟢 OK (${cts.ok})`},{k:"nostock",l:`🚫 Sin stock (${cts.nostock})`}]
          .map(f=><button key={f.k} onClick={()=>setFilter(f.k)} style={{background:filter===f.k?T.accDim:"transparent",border:`1px solid ${filter===f.k?T.accent+"44":T.border}`,color:filter===f.k?T.accent:T.txtSub,borderRadius:8,padding:"7px 14px",fontSize:12,fontWeight:700,cursor:"pointer",transition:"all .15s"}}>{f.l}</button>)}
        <div style={{flex:1}}/>
        <input value={search} onChange={e=>setSearch(e.target.value)} placeholder="🔍  Buscar producto, código, categoría..."
          style={{background:T.surf,border:`1px solid ${T.border}`,borderRadius:9,padding:"8px 14px",color:T.txt,fontSize:13,width:260,transition:"border-color .15s,box-shadow .15s"}}/>
      </div>

      <Card>
        {enriched.length===0
          ?<div style={{padding:"3rem",textAlign:"center"}}><p style={{fontSize:36,marginBottom:10}}>📭</p><p style={{fontWeight:700,fontSize:14}}>Sin productos en esta categoría</p></div>
          :<div style={{overflowX:"auto"}}>
            <table style={{width:"100%",borderCollapse:"collapse"}}>
              <thead><tr>
                <TH label="Prox. venc."/>
                <TH col="name"       label="Producto"/>
                <TH col="barcode"    label="Código"/>
                <TH col="category"   label="Cat."/>
                <TH label="Lotes"    align="center"/>
                <TH col="qty"        label="Stock" align="center"/>
                <TH label="S.mín"    align="center"/>
                <TH col="days"       label="Días"  align="center"/>
                <TH label="Acciones"/>
              </tr></thead>
              <tbody>
                {enriched.map((p,i)=>(
                  <tr key={p.id} className="row" style={{background:i%2?T.surf:T.surf2,transition:"background .1s"}}>
                    <td style={{padding:"10px 12px"}}><Badge st={p.st}/></td>
                    <td style={{padding:"10px 12px",fontWeight:600,fontSize:13,whiteSpace:"nowrap"}}>{p.name}</td>
                    <td style={{padding:"10px 12px",fontFamily:T.mono,fontSize:11,color:T.txtSub}}>{p.barcode||"—"}</td>
                    <td style={{padding:"10px 12px",fontSize:12,color:T.txtSub}}>{p.category||"—"}</td>
                    <td style={{padding:"10px 12px",textAlign:"center"}}>
                      <button onClick={()=>setBatchP(p)} style={{background:T.purDim,border:`1px solid ${T.purple}30`,color:T.purple,borderRadius:6,padding:"3px 10px",fontSize:11,fontWeight:700,cursor:"pointer"}}>
                        {p.batchCount} lote{p.batchCount!==1?"s":""}
                      </button>
                    </td>
                    <td style={{padding:"10px 12px",textAlign:"center",fontWeight:900,color:p.ss.color,fontSize:15,fontFamily:T.mono}}>{p.qty}</td>
                    <td style={{padding:"10px 12px",textAlign:"center",fontFamily:T.mono,fontSize:12,color:T.txtMuted}}>{p.minStock||5}</td>
                    <td style={{padding:"10px 12px",textAlign:"center",fontWeight:900,color:p.st.color,fontSize:14,fontFamily:T.mono}}>{p.days>=999?"—":p.days<=0?"VENC":p.days}</td>
                    <td style={{padding:"10px 12px"}}>
                      <div style={{display:"flex",gap:6}}>
                        <button className="editbtn" onClick={()=>setEditP(p)} style={{background:"transparent",border:`1px solid ${T.blue}35`,color:T.blue,borderRadius:7,padding:"4px 10px",fontSize:11,fontWeight:700,cursor:"pointer",transition:"all .15s"}}>Editar</button>
                        <button className="delbtn" onClick={()=>setConfirmId(p.id)} style={{background:"transparent",border:`1px solid ${T.red}35`,color:T.red,borderRadius:7,padding:"4px 10px",fontSize:11,fontWeight:700,cursor:"pointer",transition:"all .15s"}}>Eliminar</button>
                      </div>
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        }
      </Card>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════
// PAGE: CAJA — FIFO sale mode
// ═══════════════════════════════════════════════════════════════════
function CajaPage({products,batches,setBatches,addMovement,push}){
  const [cartLines,setCartLines]=useState([]);  // [{product, qty}]
  const [raw,setRaw]=useState("");
  const [qtyInput,setQtyInput]=useState("1");
  const [notFound,setNotFound]=useState("");
  const [anim,setAnim]=useState(false);
  const [ticket,setTicket]=useState(null);
  const [sales,setSales]=useState(()=>db.get("vcf_sales_tmp",[]));
  const bRef=useRef(null);
  useEffect(()=>setTimeout(()=>bRef.current?.focus(),80),[]);

  const addToCart=useCallback((code)=>{
    code=code.trim();
    if(!code)return;
    const prod=products.find(p=>p.barcode===code);
    if(!prod){setNotFound(code);setAnim(true);setTimeout(()=>setAnim(false),500);push(`Código "${code}" no registrado.`,"warn");setRaw("");return;}
    setNotFound("");
    const available=productStock(prod.id,batches);
    const qty=Math.max(1,parseInt(qtyInput)||1);
    // Check if selling expired batch warning
    const pb=productBatches(prod.id,batches);
    if(pb.length>0&&daysUntil(pb[0].expiry)<=0) push(`⚠️ "${prod.name}" — el lote más próximo está VENCIDO.`,"error");
    else if(pb.length>0&&daysUntil(pb[0].expiry)<=7) push(`⚠️ "${prod.name}" vence en ${daysUntil(pb[0].expiry)} días.`,"warn");
    if(available===0){push(`"${prod.name}" sin stock disponible.`,"error");setRaw("");return;}
    setCartLines(prev=>{
      const idx=prev.findIndex(l=>l.product.id===prod.id);
      if(idx>=0){
        const updated=[...prev];
        const newQty=updated[idx].qty+qty;
        if(newQty>available){push(`Stock insuficiente. Máximo disponible: ${available}.`,"error");return prev;}
        updated[idx]={...updated[idx],qty:newQty};
        return updated;
      }
      if(qty>available){push(`Stock insuficiente. Máximo disponible: ${available}.`,"error");setRaw("");return prev;}
      return [...prev,{product:prod,qty}];
    });
    setAnim(true);setTimeout(()=>setAnim(false),350);
    setRaw("");setQtyInput("1");
    setTimeout(()=>bRef.current?.focus(),60);
  },[products,batches,qtyInput,push]);

  const changeQty=(prodId,delta)=>setCartLines(prev=>{
    const prod=products.find(p=>p.id===prodId);
    const available=prod?productStock(prodId,batches):0;
    return prev.map(l=>{
      if(l.product.id!==prodId)return l;
      const nq=l.qty+delta;
      if(nq<=0)return null;
      if(nq>available){push(`Stock máximo: ${available}.`,"warn");return l;}
      return{...l,qty:nq};
    }).filter(Boolean);
  });

  const totalUnits=cartLines.reduce((a,l)=>a+l.qty,0);
  const stockIssues=cartLines.filter(l=>productStock(l.product.id,batches)<l.qty);

  const confirmSale=()=>{
    if(cartLines.length===0||stockIssues.length>0)return;
    const ts=Date.now();
    const saleId=uid();
    const saleLines=[];
    const allMovements=[];

    // ── PASS 1: simulate the whole sale against a working copy, validate everything FIRST.
    // Nothing is written to real state until we know every line can be fulfilled.
    let workingBatches=[...batches];
    let allOk=true;
    let failedProduct="";

    for(const line of cartLines){
      const pb=sortFifo(workingBatches.filter(b=>b.productId===line.product.id));
      const {consumed,updated,ok}=fifoConsume(pb,line.qty);
      if(!ok){ allOk=false; failedProduct=line.product.name; break; }
      workingBatches=workingBatches.filter(b=>b.productId!==line.product.id);
      workingBatches=[...workingBatches,...updated];
      saleLines.push({productId:line.product.id,productName:line.product.name,barcode:line.product.barcode,qty:line.qty,batches:consumed});
      consumed.forEach(c=>{
        allMovements.push({id:uid(),type:"salida",qty:c.qty,productId:line.product.id,productName:line.product.name,batchId:c.batchId,batchExpiry:c.expiry,note:`Venta #${saleId.slice(-4).toUpperCase()}`,saleId,ts});
      });
    }

    if(!allOk){
      push(`No se pudo completar la venta: stock insuficiente de "${failedProduct}".`,"error");
      return;
    }

    // ── PASS 2: everything validated — commit atomically.
    setBatches(workingBatches);
    allMovements.forEach(m=>addMovement(m));
    const sale={id:saleId,ts,lines:saleLines,totalUnits};
    setSales(prev=>{ const next=[sale,...prev].slice(0,100); db.set("vcf_sales_tmp",next); return next; });
    setTicket(sale);
    setCartLines([]);setRaw("");setQtyInput("1");
  };

  if(ticket)return(
    <div className="page" style={{maxWidth:480,margin:"0 auto"}}>
      <Card sx={{padding:"2rem",display:"flex",flexDirection:"column",gap:"1.25rem",alignItems:"center",textAlign:"center"}}>
        <div style={{width:56,height:56,borderRadius:"50%",background:T.accDim,border:`1px solid ${T.accent}30`,display:"flex",alignItems:"center",justifyContent:"center",fontSize:28}}>✓</div>
        <div>
          <p style={{fontWeight:900,fontSize:20,color:T.accent,letterSpacing:"-0.5px"}}>¡Venta registrada!</p>
          <p style={{color:T.txtSub,fontSize:13,marginTop:4}}>Ticket #{ticket.id.slice(-4).toUpperCase()} · {fmtDT(ticket.ts)}</p>
        </div>
        <div style={{width:"100%",background:T.surf2,border:`1px solid ${T.border}`,borderRadius:10,padding:"1rem",textAlign:"left",display:"flex",flexDirection:"column",gap:6}}>
          {ticket.lines.map((l,i)=>(
            <div key={i}>
              <div style={{display:"flex",justifyContent:"space-between",padding:"5px 0",borderBottom:i<ticket.lines.length-1?`1px solid ${T.border}`:"none"}}>
                <span style={{fontSize:13,fontWeight:600}}>{l.productName}</span>
                <span style={{fontFamily:T.mono,color:T.accent,fontWeight:700}}>×{l.qty}</span>
              </div>
              {l.batches.length>1&&l.batches.map((b,j)=>(
                <div key={j} style={{display:"flex",justifyContent:"space-between",padding:"2px 0 2px 12px"}}>
                  <span style={{fontSize:11,color:T.txtSub}}>Lote {fmtDate(b.expiry)}</span>
                  <span style={{fontFamily:T.mono,fontSize:11,color:T.txtMuted}}>×{b.qty}</span>
                </div>
              ))}
            </div>
          ))}
          <div style={{display:"flex",justifyContent:"space-between",paddingTop:10,marginTop:4,borderTop:`1px solid ${T.border}`}}>
            <span style={{fontSize:12,color:T.txtSub,fontWeight:700,textTransform:"uppercase",letterSpacing:"0.05em"}}>Total unidades</span>
            <span style={{fontFamily:T.mono,fontWeight:900,fontSize:16}}>{ticket.totalUnits}</span>
          </div>
        </div>
        <div style={{background:T.accDim,border:`1px solid ${T.accent}28`,borderRadius:9,padding:"10px 14px",width:"100%",textAlign:"left"}}>
          <p style={{fontSize:12,color:T.accent,fontWeight:700}}>✓ Stock descontado automáticamente con FIFO</p>
          <p style={{fontSize:11,color:T.txtSub,marginTop:3}}>El lote más próximo a vencer fue consumido primero.</p>
        </div>
        <Btn sx={{width:"100%",padding:"12px",fontSize:14}} onClick={()=>{setTicket(null);setTimeout(()=>bRef.current?.focus(),80);}}>✓ Nueva venta</Btn>
      </Card>
    </div>
  );

  return(
    <div className="page">
      <div style={{marginBottom:20,display:"flex",alignItems:"flex-start",justifyContent:"space-between",flexWrap:"wrap",gap:12}}>
        <div>
          <h1 style={{fontSize:22,fontWeight:900,letterSpacing:"-0.5px"}}>Modo caja</h1>
          <p style={{color:T.txtSub,fontSize:13,marginTop:4}}>Escaneo de ventas con descuento automático FIFO</p>
        </div>
        {sales.length>0&&<Chip color={T.txtSub} dim={T.surf2}>{sales.length} venta{sales.length!==1?"s":""} registrada{sales.length!==1?"s":""}</Chip>}
      </div>

      <div style={{display:"grid",gridTemplateColumns:"1fr 360px",gap:16,alignItems:"start"}}>
        <div style={{display:"flex",flexDirection:"column",gap:14}}>
          {/* Scanner */}
          <Card sx={{padding:"1.25rem",border:`2px solid ${anim&&!notFound?T.accent:notFound?T.red:T.border}`,transition:"border-color .3s"}}>
            <Lbl>Scanner de venta</Lbl>
            <div style={{display:"flex",gap:10,alignItems:"flex-end"}}>
              <div style={{flex:1}}>
                <p style={{fontSize:11,color:T.txtSub,marginBottom:5,fontWeight:600}}>Código de barras</p>
                <input ref={bRef} style={{background:T.bg,border:`2px solid ${notFound?T.red:T.accent}`,borderRadius:10,padding:"12px 16px",color:T.txt,fontSize:18,width:"100%",fontFamily:T.mono,letterSpacing:"2px",transition:"border-color .2s"}}
                  placeholder="▌ Esperando scanner..." value={raw}
                  onChange={e=>{setRaw(e.target.value);setNotFound("");}}
                  onKeyDown={e=>e.key==="Enter"&&raw.trim()&&addToCart(raw)}/>
              </div>
              <div style={{width:88,flexShrink:0}}>
                <p style={{fontSize:11,color:T.txtSub,marginBottom:5,fontWeight:600}}>Cantidad</p>
                <input type="number" min="1" step="1"
                  style={{background:T.bg,border:`1px solid ${T.border}`,borderRadius:10,padding:"12px 8px",color:T.txt,fontSize:18,width:"100%",fontFamily:T.mono,textAlign:"center",fontWeight:700}}
                  value={qtyInput} onChange={e=>setQtyInput(e.target.value)}
                  onBlur={()=>{ if(!qtyInput||parseInt(qtyInput)<1) setQtyInput("1"); }}
                  onKeyDown={e=>e.key==="Enter"&&raw.trim()&&addToCart(raw)}/>
              </div>
            </div>
            {notFound&&<div style={{marginTop:10,background:T.redDim,border:`1px solid ${T.red}28`,borderRadius:8,padding:"8px 12px",display:"flex",gap:8}}>
              <span>⚠️</span>
              <p style={{fontSize:12,color:T.red,fontWeight:600}}>Código <span style={{fontFamily:T.mono}}>{notFound}</span> no encontrado en Vencify.</p>
            </div>}
          </Card>

          {/* Cart */}
          <Card>
            <CardHead
              title={cartLines.length>0?`🛒 Carrito — ${cartLines.length} producto${cartLines.length!==1?"s":""}  ·  ${totalUnits} unidades`:"🛒 Carrito vacío"}
              right={cartLines.length>0&&<button onClick={()=>setCartLines([])} style={{background:"transparent",border:`1px solid ${T.red}35`,color:T.red,borderRadius:7,padding:"4px 10px",fontSize:11,fontWeight:700,cursor:"pointer"}}>Cancelar</button>}
            />
            {cartLines.length===0
              ?<div style={{padding:"2.5rem",textAlign:"center"}}>
                  <p style={{fontSize:36,marginBottom:10}}>🛒</p>
                  <p style={{fontWeight:600,color:T.txtSub,fontSize:13}}>Escaneá un producto para comenzar</p>
                </div>
              :cartLines.map((line,i)=>{
                const available=productStock(line.product.id,batches);
                const pb=productBatches(line.product.id,batches);
                const nearestExp=pb.length>0?pb[0].expiry:null;
                const days=nearestExp?daysUntil(nearestExp):999;
                const st=statusOf(days);
                const overStock=line.qty>available;
                return(
                  <div key={line.product.id} className="row" style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"12px 16px",borderBottom:i<cartLines.length-1?`1px solid ${T.border}`:"none",transition:"background .1s",gap:10,background:overStock?T.redDim:undefined}}>
                    <div style={{flex:1,minWidth:0}}>
                      <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:3,flexWrap:"wrap"}}>
                        <p style={{fontWeight:700,fontSize:13}}>{line.product.name}</p>
                        {days<=15&&<Badge st={st}/>}
                        {overStock&&<Chip color={T.red} dim={T.redDim}>Stock insuf.</Chip>}
                      </div>
                      <p style={{fontSize:11,color:T.txtSub}}>
                        Stock disponible: <span style={{fontWeight:700,color:stockSt(available).color}}>{available}</span>
                        {pb.length>1&&<> · <span style={{color:T.purple}}>{pb.length} lotes</span></>}
                        {" · "}FIFO → vence {fmtDate(nearestExp)}
                      </p>
                    </div>
                    <div style={{display:"flex",alignItems:"center",gap:8,flexShrink:0}}>
                      <button onClick={()=>changeQty(line.product.id,-1)} style={{width:28,height:28,borderRadius:7,background:T.surf2,border:`1px solid ${T.border}`,color:T.txt,fontWeight:900,fontSize:16,cursor:"pointer",display:"flex",alignItems:"center",justifyContent:"center"}}>−</button>
                      <span style={{fontFamily:T.mono,fontWeight:900,fontSize:16,color:overStock?T.red:T.txt,minWidth:24,textAlign:"center"}}>{line.qty}</span>
                      <button onClick={()=>changeQty(line.product.id,1)} style={{width:28,height:28,borderRadius:7,background:T.surf2,border:`1px solid ${T.border}`,color:T.txt,fontWeight:900,fontSize:16,cursor:"pointer",display:"flex",alignItems:"center",justifyContent:"center"}}>+</button>
                      <button onClick={()=>setCartLines(p=>p.filter(l=>l.product.id!==line.product.id))} style={{width:28,height:28,borderRadius:7,background:"transparent",border:`1px solid ${T.red}35`,color:T.red,fontWeight:900,fontSize:14,cursor:"pointer",display:"flex",alignItems:"center",justifyContent:"center"}}>×</button>
                    </div>
                  </div>
                );
              })
            }
          </Card>
        </div>

        {/* Summary panel */}
        <div style={{display:"flex",flexDirection:"column",gap:14,position:"sticky",top:28}}>
          <Card sx={{padding:"1.25rem"}}>
            <Lbl>Resumen de venta</Lbl>
            <div style={{display:"flex",flexDirection:"column",gap:10,margin:"12px 0 16px"}}>
              <div style={{display:"flex",justifyContent:"space-between"}}>
                <span style={{color:T.txtSub,fontSize:13}}>Productos distintos</span>
                <span style={{fontFamily:T.mono,fontWeight:700,fontSize:15}}>{cartLines.length}</span>
              </div>
              <div style={{display:"flex",justifyContent:"space-between",alignItems:"center"}}>
                <span style={{color:T.txtSub,fontSize:13}}>Total unidades</span>
                <span style={{fontFamily:T.mono,fontWeight:900,color:T.accent,fontSize:24,letterSpacing:"-1px"}}>{totalUnits}</span>
              </div>
            </div>
            <Hr/>
            {/* FIFO preview */}
            {cartLines.length>0&&(
              <div style={{marginTop:12,display:"flex",flexDirection:"column",gap:8}}>
                <p style={{fontSize:11,fontWeight:800,color:T.purple,textTransform:"uppercase",letterSpacing:"0.06em"}}>Preview FIFO</p>
                {cartLines.map(line=>{
                  const pb=productBatches(line.product.id,batches);
                  const {consumed}=fifoConsume(pb,line.qty);
                  return consumed.map((c,i)=>(
                    <div key={i} style={{display:"flex",justifyContent:"space-between",fontSize:11,padding:"4px 8px",background:T.purDim,borderRadius:6}}>
                      <span style={{color:T.txtSub,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap",maxWidth:160}}>{line.product.name} <span style={{color:T.purple}}>({fmtDate(c.expiry)})</span></span>
                      <span style={{fontFamily:T.mono,color:T.purple,fontWeight:700,flexShrink:0}}>−{c.qty}</span>
                    </div>
                  ));
                })}
              </div>
            )}
            {stockIssues.length>0&&(
              <div style={{background:T.redDim,border:`1px solid ${T.red}28`,borderRadius:9,padding:"10px 12px",marginTop:12}}>
                <p style={{color:T.red,fontWeight:700,fontSize:12,marginBottom:4}}>⚠️ Stock insuficiente</p>
                {stockIssues.map(l=><p key={l.product.id} style={{color:T.red,fontSize:11}}>• {l.product.name}: pedís {l.qty}, hay {productStock(l.product.id,batches)}</p>)}
              </div>
            )}
            <Btn
              sx={{width:"100%",padding:"13px",fontSize:15,marginTop:14,opacity:cartLines.length===0||stockIssues.length>0?0.4:1}}
              onClick={confirmSale} disabled={cartLines.length===0||stockIssues.length>0}>
              {cartLines.length===0?"Agregá productos":"✓ Confirmar venta"}
            </Btn>
            {cartLines.length>0&&<p style={{color:T.txtMuted,fontSize:11,textAlign:"center",marginTop:8}}>FIFO: se descuenta el lote más próximo a vencer</p>}
          </Card>

          {sales.length>0&&(
            <Card>
              <CardHead title="Últimas ventas"/>
              {sales.slice(0,6).map((s,i)=>(
                <div key={s.id} className="row" style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"10px 14px",borderBottom:i<Math.min(sales.length,6)-1?`1px solid ${T.border}`:"none",transition:"background .1s"}}>
                  <div>
                    <p style={{fontSize:12,fontWeight:600}}>#{s.id.slice(-4).toUpperCase()}</p>
                    <p style={{fontSize:10,color:T.txtSub,marginTop:1}}>{fmtDT(s.ts)} · {s.lines.length} prod.</p>
                  </div>
                  <span style={{fontFamily:T.mono,fontWeight:900,color:T.accent,fontSize:13}}>{s.totalUnits}u</span>
                </div>
              ))}
            </Card>
          )}
        </div>
      </div>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════
// PAGE: STOCK
// ═══════════════════════════════════════════════════════════════════
function StockPage({products,batches,movements,setBatches,addMovement,push}){
  const [tab,setTab]=useState("alerts");
  const [batchP,setBatchP]=useState(null);

  const enriched=products.map(p=>{
    const pb=productBatches(p.id,batches);
    const qty=pb.reduce((a,b)=>a+b.qty,0);
    return{...p,qty,batchCount:pb.length,ss:stockSt(qty),pb};
  });
  const noStock=enriched.filter(p=>p.qty===0);
  const lowStock=enriched.filter(p=>p.qty>0&&p.qty<=(p.minStock||5));
  const totIn=movements.filter(m=>m.type==="entrada").reduce((a,m)=>a+m.qty,0);
  const totOut=movements.filter(m=>m.type==="salida").reduce((a,m)=>a+m.qty,0);

  const Tab=({id,l,ct})=><button className="tb" onClick={()=>setTab(id)} style={{padding:"8px 16px",borderRadius:8,background:tab===id?T.accDim:"transparent",border:`1px solid ${tab===id?T.accent+"44":T.border}`,color:tab===id?T.accent:T.txtSub,fontWeight:700,fontSize:12,cursor:"pointer",transition:"all .15s",display:"flex",alignItems:"center",gap:7}}>
    {l}{ct!==undefined&&<span style={{background:tab===id?T.accent+"33":T.surf2,color:tab===id?T.accent:T.txtSub,borderRadius:20,padding:"0 7px",fontSize:10,fontWeight:800}}>{ct}</span>}
  </button>;

  const PRow=({p})=>(
    <div className="row" style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"12px 18px",borderBottom:`1px solid ${T.border}`,transition:"background .1s"}}>
      <div style={{display:"flex",alignItems:"center",gap:12,minWidth:0}}>
        <div style={{width:36,height:36,borderRadius:9,background:p.ss.dim,border:`1px solid ${p.ss.color}25`,display:"flex",alignItems:"center",justifyContent:"center",fontSize:18,flexShrink:0}}>{p.ss.dot}</div>
        <div style={{minWidth:0}}>
          <p style={{fontWeight:600,fontSize:13,whiteSpace:"nowrap",overflow:"hidden",textOverflow:"ellipsis"}}>{p.name}</p>
          <p style={{fontSize:11,color:T.txtSub,marginTop:2}}>{p.category||"—"} · <span style={{fontFamily:T.mono}}>{p.barcode||"—"}</span> · {p.batchCount} lote{p.batchCount!==1?"s":""}</p>
        </div>
      </div>
      <div style={{display:"flex",alignItems:"center",gap:12,flexShrink:0,marginLeft:12}}>
        <div style={{textAlign:"right"}}>
          <p style={{fontWeight:900,color:p.ss.color,fontSize:20,fontFamily:T.mono,letterSpacing:"-1px",lineHeight:1}}>{p.qty}</p>
          <p style={{fontSize:10,color:T.txtMuted,marginTop:2}}>mín: {p.minStock||5}</p>
        </div>
        <Btn v="purple" sx={{padding:"6px 12px",fontSize:12}} onClick={()=>setBatchP(p)}>Ver lotes</Btn>
      </div>
    </div>
  );

  return(
    <div className="page">
      {batchP&&<BatchModal product={batchP} batches={batches}
        onAddBatch={b=>{setBatches(prev=>[...prev,b]);addMovement({id:uid(),type:"entrada",qty:b.qty,productId:batchP.id,productName:batchP.name,batchId:b.id,batchExpiry:b.expiry,note:"Lote manual",ts:Date.now()});push(`✓ ${b.qty} unidades registradas — vencen ${fmtDate(b.expiry)}.`);}}
        onRemoveBatch={bid=>{const b=batches.find(x=>x.id===bid);setBatches(prev=>prev.filter(x=>x.id!==bid));push(`Lote eliminado.`,"warn");}}
        onClose={()=>setBatchP(null)}/>}

      <div style={{marginBottom:24}}><h1 style={{fontSize:22,fontWeight:900,letterSpacing:"-0.5px"}}>Control de stock</h1><p style={{color:T.txtSub,fontSize:13,marginTop:4}}>Gestión de lotes FIFO · entradas, salidas e historial</p></div>

      <div style={{display:"grid",gridTemplateColumns:"repeat(4,1fr)",gap:12,marginBottom:20}}>
        {[{l:"Sin stock",v:noStock.length,c:T.red,d:T.redDim,i:"🚫"},{l:"Stock bajo",v:lowStock.length,c:T.yellow,d:T.yelDim,i:"⚠️"},{l:"Total entrado",v:totIn,c:T.accent,d:T.accDim,i:"📥"},{l:"Total salido",v:totOut,c:T.blue,d:T.blueDim,i:"📤"}]
          .map(s=><div key={s.l} style={{background:s.d,border:`1px solid ${s.c}18`,borderRadius:14,padding:"16px"}}>
            <span style={{fontSize:20}}>{s.i}</span>
            <p style={{fontSize:30,fontWeight:900,color:s.c,letterSpacing:"-1px",lineHeight:1,marginTop:6}}>{s.v}</p>
            <p style={{fontSize:11,color:T.txtSub,fontWeight:700,textTransform:"uppercase",letterSpacing:"0.05em",marginTop:4}}>{s.l}</p>
          </div>)}
      </div>

      <div style={{display:"flex",gap:8,marginBottom:16,flexWrap:"wrap"}}>
        <Tab id="alerts"  l="🚨 Alertas"    ct={noStock.length+lowStock.length}/>
        <Tab id="all"     l="📦 Inventario"/>
        <Tab id="history" l="📋 Historial"   ct={movements.length}/>
      </div>

      {tab==="alerts"&&(
        <div style={{display:"flex",flexDirection:"column",gap:12}}>
          {noStock.length>0&&<Card><CardHead title="🚫 Sin stock" sub={`${noStock.length} agotado${noStock.length!==1?"s":""}`} right={<Chip color={T.red} dim={T.redDim}>{noStock.length}</Chip>}/>{noStock.map(p=><PRow key={p.id} p={p}/>)}</Card>}
          {lowStock.length>0&&<Card><CardHead title="⚠️ Stock bajo" sub={`${lowStock.length} por debajo del mínimo`} right={<Chip color={T.yellow} dim={T.yelDim}>{lowStock.length}</Chip>}/>{lowStock.map(p=><PRow key={p.id} p={p}/>)}</Card>}
          {noStock.length===0&&lowStock.length===0&&<Card sx={{padding:"3rem",textAlign:"center"}}><p style={{fontSize:36,marginBottom:12}}>🎉</p><p style={{fontWeight:700,fontSize:15}}>Sin alertas de stock</p><p style={{color:T.txtSub,fontSize:13,marginTop:6}}>Todo el inventario tiene stock suficiente.</p></Card>}
        </div>
      )}

      {tab==="all"&&(
        <Card><CardHead title="Inventario completo" sub={`${products.length} productos · ${batches.length} lotes activos`}/>
          {enriched.length===0?<div style={{padding:"2rem",textAlign:"center",color:T.txtSub}}>Sin productos.</div>
            :enriched.slice().sort((a,b)=>a.qty-b.qty).map(p=><PRow key={p.id} p={p}/>)}
        </Card>
      )}

      {tab==="history"&&(
        <Card><CardHead title="Historial de movimientos" sub={`${movements.length} registros`}/>
          {movements.length===0?<div style={{padding:"2rem",textAlign:"center",color:T.txtSub}}>Sin movimientos.</div>
            :movements.slice().sort((a,b)=>b.ts-a.ts).map((m,i)=>(
              <div key={m.id} className="row" style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"11px 18px",borderBottom:`1px solid ${T.border}`,transition:"background .1s"}}>
                <div style={{display:"flex",alignItems:"center",gap:12,minWidth:0}}>
                  <div style={{width:32,height:32,borderRadius:8,background:m.type==="entrada"?T.accDim:T.redDim,display:"flex",alignItems:"center",justifyContent:"center",fontSize:16,flexShrink:0}}>{m.type==="entrada"?"📥":"📤"}</div>
                  <div style={{minWidth:0}}>
                    <p style={{fontWeight:600,fontSize:13,whiteSpace:"nowrap",overflow:"hidden",textOverflow:"ellipsis"}}>{m.productName}</p>
                    <p style={{fontSize:11,color:T.txtSub,marginTop:1}}>
                      {fmtDT(m.ts)}
                      {m.batchExpiry&&<> · Lote <span style={{fontFamily:T.mono}}>{fmtDate(m.batchExpiry)}</span></>}
                      {m.note&&<> · {m.note}</>}
                    </p>
                  </div>
                </div>
                <div style={{display:"flex",alignItems:"center",gap:10,flexShrink:0,marginLeft:12}}>
                  <span style={{fontWeight:900,color:m.type==="entrada"?T.accent:T.red,fontSize:16,fontFamily:T.mono}}>{m.type==="entrada"?"+":"-"}{m.qty}</span>
                  <Chip color={m.type==="entrada"?T.accent:T.red} dim={m.type==="entrada"?T.accDim:T.redDim}>{m.type==="entrada"?"ENTRADA":"SALIDA"}</Chip>
                </div>
              </div>
            ))
          }
        </Card>
      )}
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════
// PAGE: PRINT
// ═══════════════════════════════════════════════════════════════════
function PrintPage({products,batches,onPrint}){
  const rows=products.map(p=>{
    const pb=productBatches(p.id,batches);
    const qty=pb.reduce((a,b)=>a+b.qty,0);
    const exp=pb.length>0?pb[0].expiry:null;
    const days=exp?daysUntil(exp):999;
    return{...p,qty,exp,days,batchCount:pb.length,st:statusOf(days)};
  }).filter(p=>p.days<=15&&p.qty>0).sort((a,b)=>a.days-b.days);

  const cts={expired:rows.filter(p=>p.days<=0).length,critical:rows.filter(p=>p.days>0&&p.days<=7).length,warning:rows.filter(p=>p.days>7&&p.days<=15).length};

  return(
    <div className="page" style={{maxWidth:680,margin:"0 auto"}}>
      <div style={{marginBottom:24}}><h1 style={{fontSize:22,fontWeight:900,letterSpacing:"-0.5px"}}>Imprimir listado</h1><p style={{color:T.txtSub,fontSize:13,marginTop:4}}>Reporte FIFO de productos próximos a vencer</p></div>
      <Card sx={{marginBottom:14}}>
        <CardHead title="Resumen" sub="Solo productos con stock que vencen en ≤15 días"/>
        <div style={{padding:"1.25rem 1.5rem",display:"flex",flexDirection:"column",gap:"1rem"}}>
          <div style={{display:"grid",gridTemplateColumns:"repeat(3,1fr)",gap:10}}>
            {[{l:"Vencidos",v:cts.expired,c:T.red},{l:"Críticos",v:cts.critical,c:T.red},{l:"Alertas",v:cts.warning,c:T.yellow}].map(s=>(
              <div key={s.l} style={{background:s.v>0?`${s.c}10`:T.surf2,border:`1px solid ${s.v>0?s.c+"28":T.border}`,borderRadius:10,padding:"14px 16px"}}>
                <div style={{fontSize:28,fontWeight:900,color:s.v>0?s.c:T.txtMuted,letterSpacing:"-1px"}}>{s.v}</div>
                <div style={{fontSize:11,color:T.txtSub,fontWeight:700,marginTop:3}}>{s.l}</div>
              </div>
            ))}
          </div>
          <Btn sx={{width:"100%",padding:"13px",fontSize:15}} onClick={onPrint}>🖨️ Imprimir ahora</Btn>
        </div>
      </Card>
      <Card>
        <CardHead title="Vista previa" right={<Chip color={T.txtSub} dim={T.surf2}>{rows.length} productos</Chip>}/>
        {rows.length===0?<div style={{padding:"2.5rem",textAlign:"center"}}><p style={{fontSize:32,marginBottom:8}}>✅</p><p style={{fontWeight:700,fontSize:14}}>Sin productos próximos a vencer</p></div>
          :rows.map((p,i)=>(
            <div key={p.id} className="row" style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"11px 18px",borderBottom:i<rows.length-1?`1px solid ${T.border}`:"none",background:i%2?T.surf:T.surf2,transition:"background .1s"}}>
              <div style={{display:"flex",alignItems:"center",gap:12}}>
                <Badge st={p.st}/>
                <div>
                  <p style={{fontWeight:600,fontSize:13}}>{p.name}</p>
                  <p style={{fontSize:11,color:T.txtSub,marginTop:1}}>{p.category||"—"} · <span style={{fontFamily:T.mono}}>{p.barcode||"—"}</span> · {p.batchCount} lote{p.batchCount!==1?"s":""} · Stock: {p.qty}</p>
                </div>
              </div>
              <div style={{textAlign:"right",flexShrink:0,marginLeft:16}}>
                <p style={{fontWeight:900,color:p.st.color,fontSize:14,fontFamily:T.mono}}>{p.days<=0?"VENCIDO":`${p.days}d`}</p>
                <p style={{fontSize:11,color:T.txtSub,fontFamily:T.mono,marginTop:1}}>{fmtDate(p.exp)}</p>
              </div>
            </div>
          ))
        }
      </Card>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════
// ROOT
// ═══════════════════════════════════════════════════════════════════
export default function Vencify(){
  useEffect(()=>{ const el=document.createElement("style");el.innerHTML=CSS;document.head.appendChild(el);return()=>document.head.removeChild(el); },[]);

  const [user,setUser]=useState(()=>{ try{return JSON.parse(localStorage.getItem("vcf_session"));}catch{return null;} });
  const [page,setPage]=useState("dashboard");
  const {list:toasts,push}=useToast();

  const pKey=user?`vcf_p_${user.id}`:"";
  const bKey=user?`vcf_b_${user.id}`:"";
  const mKey=user?`vcf_m_${user.id}`:"";

  const [products,setProductsRaw]=useState(()=>user?db.get(pKey,[]):[]);
  const [batches, setBatchesRaw] =useState(()=>user?db.get(bKey,[]):[]);
  const [movements,setMovementsRaw]=useState(()=>user?db.get(mKey,[]):[]);

  const setProducts =useCallback(fn=>setProductsRaw(p=>{ const n=typeof fn==="function"?fn(p):fn; db.set(pKey,n); return n; }),[pKey]);
  const setBatches  =useCallback(fn=>setBatchesRaw(p=>{ const n=typeof fn==="function"?fn(p):fn; db.set(bKey,n); return n; }),[bKey]);
  const setMovements=useCallback(fn=>setMovementsRaw(p=>{ const n=typeof fn==="function"?fn(p):fn; db.set(mKey,n); return n; }),[mKey]);
  const addMovement =useCallback(m=>setMovements(p=>[m,...p]),[setMovements]);

  useEffect(()=>{
    if(user){ setProductsRaw(db.get(`vcf_p_${user.id}`,[])); setBatchesRaw(db.get(`vcf_b_${user.id}`,[])); setMovementsRaw(db.get(`vcf_m_${user.id}`,[])); }
  },[user?.id]);

  useEffect(()=>{ const h=e=>{if(e.key==="F2"){e.preventDefault();setPage("scan");}};window.addEventListener("keydown",h);return()=>window.removeEventListener("keydown",h); },[]);

  const counts={
    all:products.length,
    expired:products.filter(p=>{ const exp=earliestExpiry(p.id,batches);return exp&&daysUntil(exp)<=0&&productStock(p.id,batches)>0; }).length,
    critical:products.filter(p=>{ const exp=earliestExpiry(p.id,batches);const d=exp?daysUntil(exp):999;return d>0&&d<=7&&productStock(p.id,batches)>0; }).length,
    warning:products.filter(p=>{ const exp=earliestExpiry(p.id,batches);const d=exp?daysUntil(exp):999;return d>7&&d<=15&&productStock(p.id,batches)>0; }).length,
    ok:products.filter(p=>{ const exp=earliestExpiry(p.id,batches);const d=exp?daysUntil(exp):999;return d>15&&productStock(p.id,batches)>0; }).length,
    noStock:products.filter(p=>productStock(p.id,batches)===0).length,
  };
  const stockAlerts=products.filter(p=>{ const q=productStock(p.id,batches);return q<=(p.minStock||5); }).length;
  const urgentTotal=counts.expired+counts.critical;

  const doPrint=()=>{ const z=document.getElementById("pzone");if(z)z.style.display="block";window.print();setTimeout(()=>{if(z)z.style.display="none";},700); };
  const handleLogin=u=>{ localStorage.setItem("vcf_session",JSON.stringify(u));setUser(u);setPage("dashboard"); };
  const handleLogout=()=>{ localStorage.removeItem("vcf_session");setUser(null); };

  if(!user)return <AuthScreen onLogin={handleLogin}/>;

  const NI=({id,icon,label,count})=>(
    <button className="nb" onClick={()=>setPage(id)} style={{display:"flex",alignItems:"center",gap:11,padding:"9px 12px",background:page===id?T.accDim:"transparent",border:`1px solid ${page===id?T.accent+"38":"transparent"}`,borderRadius:10,color:page===id?T.accent:T.txtSub,fontWeight:page===id?700:500,fontSize:13,cursor:"pointer",width:"100%",textAlign:"left",transition:"all .15s"}}>
      <span style={{fontSize:14,width:18,textAlign:"center",flexShrink:0}}>{icon}</span>
      <span style={{flex:1}}>{label}</span>
      {count>0&&<span style={{background:T.red,color:"#fff",borderRadius:20,padding:"1px 7px",fontSize:10,fontWeight:900,lineHeight:"16px"}}>{count}</span>}
    </button>
  );

  return(
    <div style={{display:"flex",minHeight:"100vh",background:T.bg}}>
      <Toasts list={toasts}/>
      <PrintZone products={products} batches={batches} storeName={user.store}/>

      <aside style={{width:224,background:T.surf,borderRight:`1px solid ${T.border}`,display:"flex",flexDirection:"column",position:"fixed",top:0,left:0,height:"100vh",zIndex:50,boxShadow:"4px 0 24px rgba(0,0,0,.25)"}}>
        <div style={{padding:"16px 14px 12px",borderBottom:`1px solid ${T.border}`}}>
          <div style={{display:"flex",alignItems:"center",gap:10}}>
            <div style={{width:30,height:30,borderRadius:8,background:`linear-gradient(135deg,${T.accent},#00B388)`,display:"flex",alignItems:"center",justifyContent:"center",fontWeight:900,color:"#000",fontSize:15,flexShrink:0,boxShadow:`0 0 0 3px ${T.accGlow}, 0 2px 8px ${T.accent}30`}}>V</div>
            <div style={{display:"flex",alignItems:"baseline",gap:6}}>
              <span style={{fontWeight:900,fontSize:16,letterSpacing:"-0.5px"}}>Vencify</span>
              <span style={{fontSize:9,color:T.txtMuted,fontWeight:700,background:T.surf2,padding:"1px 5px",borderRadius:4,fontFamily:T.mono}}>FIFO</span>
            </div>
          </div>
          <div style={{marginTop:10,paddingLeft:40}}>
            <p style={{fontSize:12,fontWeight:700,color:T.txt,whiteSpace:"nowrap",overflow:"hidden",textOverflow:"ellipsis"}}>{user.store}</p>
            <p style={{fontSize:10,color:T.txtMuted,marginTop:1,whiteSpace:"nowrap",overflow:"hidden",textOverflow:"ellipsis"}}>{user.email}</p>
          </div>
        </div>

        <nav style={{flex:1,padding:"10px 8px",display:"flex",flexDirection:"column",gap:2,overflowY:"auto"}}>
          <p style={{fontSize:9,fontWeight:900,color:T.txtMuted,textTransform:"uppercase",letterSpacing:"0.1em",padding:"8px 6px 4px"}}>Principal</p>
          <NI id="dashboard" icon="📊" label="Dashboard"        count={urgentTotal}/>
          <NI id="scan"      icon="📷" label="Escanear lotes"/>
          <NI id="caja"      icon="🛒" label="Modo caja"/>
          <NI id="list"      icon="📋" label="Productos"/>
          <NI id="stock"     icon="📦" label="Stock y lotes"    count={stockAlerts}/>
          <NI id="print"     icon="🖨️" label="Imprimir"/>
          <div style={{height:1,background:T.border,margin:"8px 6px"}}/>
          <p style={{fontSize:9,fontWeight:900,color:T.txtMuted,textTransform:"uppercase",letterSpacing:"0.1em",padding:"4px 6px"}}>Sistema</p>
          <NI id="install"   icon="⚙️" label="Instalar en PC"/>
        </nav>

        {(urgentTotal+stockAlerts)>0&&(
          <div style={{margin:"0 8px 8px",background:T.redDim,border:`1px solid ${T.red}28`,borderRadius:10,padding:"11px"}}>
            <p style={{color:T.red,fontWeight:800,fontSize:11,marginBottom:5}}>⚠️ Atención</p>
            {counts.expired>0&&<p style={{color:T.red,fontSize:11,marginBottom:2}}>• {counts.expired} vencido{counts.expired!==1?"s":""}</p>}
            {counts.critical>0&&<p style={{color:T.red,fontSize:11,marginBottom:2}}>• {counts.critical} crítico{counts.critical!==1?"s":""}</p>}
            {stockAlerts>0&&<p style={{color:T.yellow,fontSize:11}}>• {stockAlerts} con stock bajo</p>}
          </div>
        )}

        <div style={{padding:"8px",borderTop:`1px solid ${T.border}`}}>
          <button onClick={handleLogout} style={{background:"transparent",border:`1px solid ${T.border}`,color:T.txtSub,borderRadius:8,padding:"8px",fontSize:12,cursor:"pointer",width:"100%",fontWeight:600}}>Cerrar sesión</button>
          <p style={{color:T.txtMuted,fontSize:10,textAlign:"center",marginTop:8}}><kbd style={{background:T.surf2,border:`1px solid ${T.border}`,borderRadius:3,padding:"0 4px",fontFamily:T.mono,fontSize:9}}>F2</kbd> → escanear</p>
        </div>
      </aside>

      <div style={{marginLeft:224,flex:1,display:"flex",justifyContent:"center",padding:"28px 32px",minHeight:"100vh",alignItems:"flex-start"}}>
        <div style={{width:"100%",maxWidth:980}}>
          {page==="dashboard"&&<Dashboard products={products} batches={batches} movements={movements} counts={counts} setPage={setPage} onPrint={doPrint} user={user}/>}
          {page==="scan"     &&<ScanPage  products={products} batches={batches} setProducts={setProducts} setBatches={setBatches} addMovement={addMovement} push={push}/>}
          {page==="caja"     &&<CajaPage  products={products} batches={batches} setBatches={setBatches} addMovement={addMovement} push={push}/>}
          {page==="list"     &&<ListPage  products={products} batches={batches} setProducts={setProducts} setBatches={setBatches} addMovement={addMovement} push={push}/>}
          {page==="stock"    &&<StockPage products={products} batches={batches} movements={movements} setBatches={setBatches} addMovement={addMovement} push={push}/>}
          {page==="print"    &&<PrintPage products={products} batches={batches} onPrint={doPrint}/>}
          {page==="install"  &&<InstallPage/>}
        </div>
      </div>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════
// PAGE: INSTALL
// ═══════════════════════════════════════════════════════════════════
function InstallPage(){
  const [copied,setCopied]=useState(null);
  const cp=(text,k)=>navigator.clipboard.writeText(text).then(()=>{setCopied(k);setTimeout(()=>setCopied(null),2000);});
  const Code=({id,code})=>(
    <div style={{position:"relative",marginTop:8}}>
      <pre style={{background:T.bg,border:`1px solid ${T.border}`,borderRadius:9,padding:"12px 14px",paddingRight:80,fontFamily:T.mono,fontSize:12,color:T.accent,overflowX:"auto",lineHeight:1.8}}>{code}</pre>
      <button onClick={()=>cp(code,id)} style={{position:"absolute",top:8,right:8,background:T.surf2,border:`1px solid ${T.border}`,color:copied===id?T.accent:T.txtSub,borderRadius:6,padding:"3px 10px",fontSize:11,fontWeight:700,cursor:"pointer"}}>{copied===id?"✓ Copiado":"Copiar"}</button>
    </div>
  );
  const Step=({n,title,sub,children})=>(
    <div style={{display:"flex",gap:16,paddingBottom:24}}>
      <div style={{flexShrink:0,display:"flex",flexDirection:"column",alignItems:"center"}}>
        <div style={{width:32,height:32,borderRadius:"50%",background:T.accDim,border:`1px solid ${T.accent}30`,display:"flex",alignItems:"center",justifyContent:"center",fontWeight:900,color:T.accent,fontSize:14}}>{n}</div>
        <div style={{flex:1,width:1,background:T.border,marginTop:6}}/>
      </div>
      <div style={{flex:1}}>
        <p style={{fontWeight:700,fontSize:14,color:T.txt,marginBottom:3}}>{title}</p>
        {sub&&<p style={{fontSize:12,color:T.txtSub,marginBottom:8,lineHeight:1.6}}>{sub}</p>}
        {children}
      </div>
    </div>
  );
  return(
    <div className="page" style={{maxWidth:660,margin:"0 auto"}}>
      <div style={{marginBottom:24}}><h1 style={{fontSize:22,fontWeight:900,letterSpacing:"-0.5px"}}>Instalar en la PC</h1><p style={{color:T.txtSub,fontSize:13,marginTop:4}}>Guía paso a paso para Windows</p></div>
      <div style={{background:T.accDim,border:`1px solid ${T.accent}28`,borderRadius:12,padding:"14px 18px",marginBottom:20,display:"flex",gap:12}}>
        <span style={{fontSize:18,flexShrink:0}}>💡</span>
        <p style={{fontSize:13,lineHeight:1.6}}>Vencify corre en el navegador de la PC. <strong style={{color:T.accent}}>No necesita internet</strong>. El scanner USB funciona automáticamente sin drivers.</p>
      </div>
      <Card sx={{padding:"1.5rem 1.75rem"}}>
        <Step n="1" title="Instalá Node.js" sub="Entrá a nodejs.org, descargá la versión LTS y ejecutá el instalador (Next a todo).">
          <div style={{background:T.bg,border:`1px solid ${T.border}`,borderRadius:9,padding:"10px 14px",display:"flex",alignItems:"center",gap:10}}>
            <span style={{fontFamily:T.mono,fontSize:12,color:T.accent,flex:1}}>https://nodejs.org</span>
            <button onClick={()=>cp("https://nodejs.org","url")} style={{background:T.surf2,border:`1px solid ${T.border}`,color:copied==="url"?T.accent:T.txtSub,borderRadius:6,padding:"3px 10px",fontSize:11,fontWeight:700,cursor:"pointer"}}>{copied==="url"?"✓":"Copiar"}</button>
          </div>
        </Step>
        <Step n="2" title="Cerrá y reabrí el CMD" sub="Importante: después de instalar Node, cerrá el CMD y abrí uno nuevo."/>
        <Step n="3" title="Verificá que Node está instalado">
          <Code id="ver" code="node --version"/>
          <p style={{fontSize:12,color:T.txtSub,marginTop:6}}>Tiene que aparecer un número como v22.x.x</p>
        </Step>
        <Step n="4" title="Creá el proyecto Vencify">
          <Code id="create" code={"npm create vite@latest vencify -- --template react\ncd vencify\nnpm install"}/>
        </Step>
        <Step n="5" title="Reemplazá el archivo principal" sub="Abrí la carpeta vencify/src/App.jsx, borrá todo el contenido y pegá el código de Vencify descargado.">
          <div style={{background:T.yelDim,border:`1px solid ${T.yellow}28`,borderRadius:9,padding:"11px 14px",display:"flex",gap:10}}>
            <span>💾</span>
            <p style={{fontSize:12,lineHeight:1.5}}>Archivo: <span style={{fontFamily:T.mono,color:T.yellow}}>vencify/src/App.jsx</span></p>
          </div>
        </Step>
        <Step n="6" title="Iniciá Vencify">
          <Code id="dev" code="npm run dev"/>
          <p style={{fontSize:12,color:T.txtSub,marginTop:6}}>Abrí <span style={{fontFamily:T.mono,color:T.accent}}>http://localhost:5173</span> en el navegador.</p>
        </Step>
        <div style={{background:T.redDim,border:`1px solid ${T.red}28`,borderRadius:10,padding:"14px 16px",display:"flex",gap:12,marginTop:8}}>
          <span style={{fontSize:18,flexShrink:0}}>⚠️</span>
          <div><p style={{fontWeight:700,fontSize:13,color:T.red,marginBottom:4}}>Scanner USB</p><p style={{fontSize:12,lineHeight:1.6}}>En "Escanear lotes" o "Modo caja", hacé click en el campo de código y apretá el gatillo. El scanner escribe el código y manda Enter automáticamente.</p></div>
        </div>
      </Card>
    </div>
  );
}
