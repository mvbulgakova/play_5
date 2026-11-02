'use strict';
// ═══════════════ «Пятый Постулат» · Глава 1 «Архив лишних точек» ═══════════════
// Играбельный срез поверх движка index.html (веха 1 концепта).
//  • Уровень — конечный набор комнат-додекаэдров {5,3,4}; все остальные комнаты замощения
//    заполнены камнем. Шейдер узнаёт комнату по «якорям»: четыре точки A_i отражаются вместе
//    с лучом, и вектор ch d(центр комнаты, A_i) однозначно задаёт комнату.
//  • Стражи и предметы живут в абсолютных координатах R^{3,1} (по одному экземпляру),
//    а не в фундаментальной области, поэтому не размножаются по всем комнатам.
//  • Пересечение луча с шаром — в замкнутой форме: ⟨x(t),C⟩ = −(A ch t + B sh t).
// Способности: геодезический рывок (ПКМ), Линза Абсолюта (V), усыпление (F).
const MISSION=(()=>{
const g=GEO.dodeca;
const PHI=(1+Math.sqrt(5))/2,UN=Math.hypot(1,PHI);
const C5=1/Math.sqrt(5),CHD=Math.sqrt(1/(1-C5)),SHD=Math.sqrt(1/(1-C5)-1);
const DELTA=Math.acosh(CHD);                       // от центра комнаты до грани ≈ 0,808
const FACES=(()=>{const U=[];for(const a of [1,-1])for(const b of [1,-1])U.push([0,a,b*PHI],[a,b*PHI,0],[b*PHI,0,a]);
  return U.map(u=>[CHD*u[0]/UN,CHD*u[1]/UN,CHD*u[2]/UN,SHD]);})();
const RF=FACES.map(refl);                           // отражения в 12 гранях базовой комнаты
// FACES[0..2] — грани N0,N1,N2, касающиеся фундаментальной области (M[0] = N0).
const ANCH=[[0.42,0.05,-0.10,1],[-0.10,0.40,0.15,1],[0.05,-0.12,0.44,1],[-0.30,-0.25,-0.20,1]].map(normalizePoint);

// ───────── вспомогательная алгебра ─────────
function linv(G){const R=new Array(16),J=[1,1,1,-1];for(let c=0;c<4;c++)for(let r=0;r<4;r++)R[c*4+r]=J[r]*G[r*4+c]*J[c];return R;}
function det4(m){const a=(r,c)=>m[c*4+r];let s=0;
  for(let c=0;c<4;c++){const k=[0,1,2,3].filter(x=>x!==c);
    s+=(c%2?-1:1)*a(0,c)*det3(a(1,k[0]),a(1,k[1]),a(1,k[2]),a(2,k[0]),a(2,k[1]),a(2,k[2]),a(3,k[0]),a(3,k[1]),a(3,k[2]));}
  return s;}
function perpAt(p,u){for(const b of [[0,1,0,0],[1,0,0,0],[0,0,1,0]]){let w=b.map((x,i)=>x+md(b,p)*p[i]);const e=md(w,u);w=w.map((x,i)=>x-e*u[i]);
  if(md(w,w)>1e-4)return tangent(w,p);}return tangent([0,1,0,0],p);}
function frameAt(p,fwd){p=normalizePoint(p);const f=tangent(fwd,p),up=perpAt(p,f);
  let r=[1,0,0,0];for(const b of [[1,0,0,0],[0,0,1,0],[0,1,0,0]]){let w=b.map((x,i)=>x+md(b,p)*p[i]);
    for(const e of [f,up]){const d=md(w,e);w=w.map((x,i)=>x-d*e[i]);}if(md(w,w)>1e-4){r=tangent(w,p);break;}}
  const M=[...r,...up,...f,...p];if(det4(M)<0)for(let i=0;i<4;i++)M[i]=-M[i];return M;}
const far=d=>{const l=Math.hypot(...d),s=Math.sinh(9);return [s*d[0]/l,s*d[1]/l,s*d[2]/l,Math.cosh(9)];};
const mid=(a,b)=>normalizePoint(a.map((x,i)=>x+b[i]));

// ───────── уровень ─────────
// [id, откуда, направление (в модели Клейна), название, лампа горит]
const ROOM_SPEC=[
  ['hub',null,null,'Атриум',1],
  ['a1','hub',[0,0.15,1],'Галерея',1],
  ['a2','a1',[0,0.3,1],'Переход',0],
  ['a3','a2',[0.5,0.6,1],'Хранилище чертежей',1],
  ['b1','hub',[1,0,0.2],'Картотека',1],
  ['b2','b1',[1,-0.2,0.4],'Дальняя картотека',0],
  ['b3','b2',[1,-1,0.5],'Зал переписи',1],
  ['c1','hub',[-1,-0.2,-0.4],'Коридор окна',0],
  ['c2','c1',[-1,-0.4,-1],'Окно на Абсолют',1],
  ['s1','a1',[1,0.3,0.5],'Чертёжная',0],
  ['s2','hub',[0,-1,0.2],'Кладовая',0],
];
let ROOMS=[];
function buildRooms(){const R=[];const find=c=>R.findIndex(r=>-md(r.c,c)<1.002);
  for(const [id,from,dir,name,lit] of ROOM_SPEC){let T;
    if(!from)T=I4();
    else{const Tf=R.find(r=>r.id===from).T,tg=far(dir);let best=null;
      for(let k=0;k<12;k++){const T2=mul(Tf,RF[k]),c2=apply(T2,O);if(find(c2)>=0)continue;const s=-md(c2,tg);if(!best||s<best.s)best={s,T2};}
      T=best.T2;}
    R.push({id,name,T,c:apply(T,O),lit0:!!lit});}
  R.forEach((r,i)=>{r.nb=[];R.forEach((q,j)=>{if(i!==j&&Math.abs(hyperbolicDistance(r.c,q.c)-2*DELTA)<0.01)r.nb.push(j);});
    r.key=ANCH.map(a=>-md(r.c,a));});
  return R;}
ROOMS=buildRooms();
const RI=id=>ROOMS.findIndex(r=>r.id===id);
const roomAt=c=>{for(let i=0;i<ROOMS.length;i++)if(-md(ROOMS[i].c,c)<1.002)return i;return -1;};
function roomFold(x){let y=x.slice(),T=I4();
  for(let it=0;it<48;it++){let bk=-1,bs=1e-12;for(let k=0;k<12;k++){const s=md(y,FACES[k]);if(s>bs){bs=s;bk=k;}}
    if(bk<0)break;y=apply(RF[bk],y);T=mul(T,RF[bk]);}
  return {y,T};}
const roomOfPoint=x=>roomAt(apply(roomFold(x).T,O));
// SDF мира в абсолютных координатах — та же логика, что в шейдере.
function sdfWorld(x,lampR){const f=roomFold(x);let z=f.y,W=f.T;
  for(let it=0;it<12;it++){let any=false;for(let k=1;k<4;k++)if(md(z,g.M[k])>0){z=apply(g.R[k],z);W=mul(W,g.R[k]);any=true;}if(!any)break;}
  let d=roomsObstacleMap(z,g,{tube:0.04,ball:0.085,lamp:lampR??0.055});
  for(let i=0;i<3;i++){const dF=Math.asinh(-md(z,FACES[i]));if(dF<d+0.02&&roomAt(apply(W,apply(RF[i],O)))<0)d=Math.min(d,dF);}
  return d;}
const sdfLOS=x=>sdfWorld(x,0.05);
function los(a,b){const d=hyperbolicDistance(a,b);if(d<0.05)return true;
  return raymarchObstacles(a,dirTo(a,b),d-0.04,sdfLOS,0.25)>=d-0.08;}
const faceCenter=(i,j)=>mid(ROOMS[i].c,ROOMS[j].c);
function beyondFace(i,j,s){const c=ROOMS[i].c;return advancePose(c,dirTo(c,ROOMS[j].c),DELTA+s).p;}
function roomPoint(b,fin,fout,r){const c=ROOMS[b].c,din=dirTo(c,fin),dout=dirTo(c,fout),dd=md(din,dout);
  const w=Math.abs(dd)>0.9?perpAt(c,din):tangent(din.map((x,i)=>x+dout[i]),c);
  return advancePose(c,w,r??0.33).p;}
function localPoint(id,off){return apply(ROOMS[RI(id)].T,normalizePoint([...off,1]));}
function bfs(a,b){if(a===b)return [a];const prev=new Map([[a,-1]]),q=[a];
  while(q.length){const x=q.shift();for(const y of ROOMS[x].nb)if(!prev.has(y)){prev.set(y,x);if(y===b){const p=[b];let z=b;while(prev.get(z)>=0){z=prev.get(z);p.unshift(z);}return p;}q.push(y);}}
  return null;}

const LEMMAS=[
  {t:'Лемма о дефекте',x:'Сумма углов треугольника меньше π. Недостача δ = π − (α + β + γ) называется дефектом, и площадь треугольника равна дефекту: S = δ (при кривизне −1). Поэтому подобных треугольников разного размера здесь нет: увеличить фигуру, не изменив её углов, нельзя.'},
  {t:'Лемма о параллелях',x:'Через точку вне прямой проходят две прямые, параллельные данной: они отделяют прямые, пересекающие её, от расходящихся. Угол между перпендикуляром и параллелью — угол параллельности Π(x), tg(Π(x)/2) = e<sup>−x</sup>. Чем дальше точка от прямой, тем меньше этот угол.'},
  {t:'Лемма о видимом размере',x:'Шар радиуса r на расстоянии d виден под углом α, где sin α = sh r / sh d. Знаменатель растёт как e<sup>d</sup>/2, поэтому через две комнаты страж — почти точка. И вы для него тоже: держитесь дальше и не стойте у ламп.'},
  {t:'Лемма о прямом додекаэдре',x:'Если отодвинуть грани правильного додекаэдра от центра так, чтобы в модели Кэли — Клейна они лежали на расстоянии h = 5<sup>−1/4</sup>, все его двугранные углы станут прямыми. Такие додекаэдры заполняют пространство по четыре у каждого ребра. Из них и сложен Архив.'},
];
const ITEM_SPEC=[
  {id:'lens',kind:3,r:0.06,room:'a3',off:[0.05,-0.30,0.10],name:'Линза Абсолюта'},
  {id:'rec',kind:4,r:0.05,room:'b3',off:[-0.10,-0.30,0.05],name:'Лист 281'},
  {id:'lem0',kind:2,r:0.04,room:'s2',off:[0.25,0.15,-0.10],lemma:0},
  {id:'lem1',kind:2,r:0.04,room:'s1',off:[-0.20,0.25,0.10],lemma:1},
  {id:'lem2',kind:2,r:0.04,room:'b2',off:[0.10,0.30,-0.15],lemma:2},
  {id:'lem3',kind:2,r:0.04,room:'c1',off:[0.20,-0.25,0.20],lemma:3},
  {id:'sh0',kind:7,r:0.035,room:'a2',off:[-0.25,-0.15,0.15]},
  {id:'sh1',kind:7,r:0.035,room:'b1',off:[0.15,0.28,-0.20]},
  {id:'sh2',kind:7,r:0.035,room:'s2',off:[-0.25,-0.20,0.10]},
  {id:'exit',kind:5,r:0.13,room:'c2',off:[0.0,0.0,0.0],exitDir:true},
];
function itemPos(it){if(it.exitDir){const c=ROOMS[RI('c2')].c;return advancePose(c,dirTo(c,ROOMS[RI('c1')].c),-0.42).p;}return localPoint(it.room,it.off);}
const ITEMS=ITEM_SPEC.map(it=>({...it,pos:itemPos(it)}));
const GUARD_SPEC=[
  {name:'Чертёжник Орт',route:['hub','a1','s1','b1']},
  {name:'Чертёжник Евтих',route:['a2','a3','s1','a1']},
  {name:'Чертёжник Пасх',route:['b1','b2','b3','b2']},
  {name:'Чертёжник Нил',route:['c1','c2'],wait:2.6},
];
function buildRoute(ids,wait){const n=ids.map(RI),W=[];
  for(let k=0;k<n.length;k++){const a=n[k],b=n[(k+1)%n.length],c=n[(k+2)%n.length];
    W.push({p:faceCenter(a,b),wait:0});W.push({p:roomPoint(b,faceCenter(a,b),faceCenter(b,c)),wait:wait??1.4});}
  return W;}

// ───────── стражи ─────────
const FOV=80*Math.PI/180,VIEW=4.5,RATE=3.0,CATCH=0.30;
class Guard{
  constructor(spec,idx){this.idx=idx;this.name=spec.name;this.route=buildRoute(spec.route,spec.wait);this.wp=1;
    this.pos=this.route[0].p.slice();this.dir=dirTo(this.pos,this.route[1].p);
    this.state='patrol';this.alert=0;this.sleep=false;this.timer=0;this.wait=0;this.goal=null;this.lastSeen=null;
    this.seenAgo=99;this.found=false;this.scan=null;this.sees=0;}
  turn(des,dt,rate){const k=1-Math.exp(-(rate??3.2)*dt);this.dir=tangent(this.dir.map((x,i)=>x*(1-k)+des[i]*k),this.pos);}
  moveTo(tg,sp,dt){const d=hyperbolicDistance(this.pos,tg);if(d<0.05)return true;const des=dirTo(this.pos,tg);this.turn(des,dt);
    if(md(this.dir,des)<Math.cos(0.5))return false;const s=Math.min(d,sp*dt);const nx=advancePose(this.pos,this.dir,s);
    this.pos=nx.p;this.dir=nx.u;return d-s<0.05;}
  nav(tg){const a=roomOfPoint(this.pos),b=roomOfPoint(tg);if(a<0||b<0||a===b)return tg;
    const p=bfs(a,b);return p&&p.length>1?beyondFace(a,p[1],0.12):tg;}
  look(dt){if(!this.scan){this.scan={d0:this.dir.slice(),pp:perpAt(this.pos,this.dir),t:0};}
    const s=this.scan;s.t+=dt;const ph=1.0*Math.sin(s.t*1.5);
    this.turn(tangent(s.d0.map((x,i)=>Math.cos(ph)*x+Math.sin(ph)*s.pp[i]),this.pos),dt,4);}
  perceive(px,lightF,motionF){const d=hyperbolicDistance(this.pos,px);if(d>VIEW)return 0;
    const ang=Math.acos(clamp(md(this.dir,dirTo(this.pos,px)),-1,1)),half=FOV/2;
    let base=ang<=half?0.55+0.45*(1-ang/half):(d<0.45?0.55:0);if(!base)return 0;
    if(!los(this.pos,px))return 0;const sh=Math.sinh(d);return base*lightF*motionF/(1+0.9*sh*sh);}
  sees_(x,maxD){const d=hyperbolicDistance(this.pos,x);if(d>maxD)return false;
    if(Math.acos(clamp(md(this.dir,dirTo(this.pos,x)),-1,1))>FOV/2)return false;return los(this.pos,x);}
  toJSON(){const o={};for(const k of ['wp','pos','dir','state','alert','sleep','timer','wait','goal','lastSeen','seenAgo','found'])o[k]=this[k];return o;}
}

// ───────── шейдер ─────────
const NK=16,NO=16;
const FS_MISSION=HEAD+`
#define NK ${NK}
#define NO ${NO}
uniform vec4 uM[4]; uniform vec4 uE1; uniform vec4 uE2; uniform vec4 uV; uniform float uBall; uniform float uCamPar;
uniform vec4 uF[3]; uniform vec4 uA[4];
uniform vec4 uK[NK]; uniform float uLit[NK]; uniform vec4 uRC[NK]; uniform int uNK;
uniform vec4 uO[NO]; uniform vec4 uOR[NO]; uniform vec4 uOU[NO]; uniform vec4 uOD[NO]; uniform vec4 uOK[NO]; uniform vec4 uOC[NO]; uniform int uNO;
uniform vec4 uMark; uniform float uMarkOn; uniform float uLens; uniform float uTime; uniform float uCosFov; uniform float uView;
const vec3 FOG=vec3(0.010,0.013,0.030);
const vec3 LAMP=vec3(1.0,0.68,0.36);
vec4 gA[4]; bool gW[3];
int roomKey(vec4 k){
  for(int j=0;j<NK;j++){ if(j>=uNK) break; vec4 r=abs(k-uK[j])/uK[j];
    if(max(max(r.x,r.y),max(r.z,r.w))<4e-3) return j; }
  return -1; }
vec4 nkey(vec4 F){ return vec4(gA[0].w-2.*md(gA[0],F)*F.w, gA[1].w-2.*md(gA[1],F)*F.w, gA[2].w-2.*md(gA[2],F)*F.w, gA[3].w-2.*md(gA[3],F)*F.w); }
float map(vec4 p){
  float a=md(p,uE1), b=md(p,uE2);
  float d=asinh(sqrt(a*a+b*b))-uTube; gId=1;
  float dv=acosh(max(-md(p,uV),1.))-uBall; if(dv<d){d=dv;gId=2;}
  float dl=acosh(max(p.w,1.))-0.055; if(dl<d){d=dl;gId=3;}
  for(int i=0;i<3;i++) if(gW[i]){ float dw=asinh(-md(p,uF[i])); if(dw<d){d=dw;gId=5+i;} }
  return d;
}` + NORMAL + MAT + `
// ── стены: обои, деревянная рама с латунным валиком, медальон-розетка в центре грани ──
float wallH(vec4 p){ float e=edgeDist(p), r=acosh(max(-md(p,uP1),1.));
  float h=0.008*smoothstep(0.045,0.06,e)*(1.-smoothstep(0.105,0.118,e));
  h+=0.003*exp(-pow((e-0.075)/0.006,2.));
  h-=0.003*exp(-pow((e-0.13)/0.006,2.));
  h+=0.006*(1.-smoothstep(0.155,0.162,r));
  h-=0.002*(1.-smoothstep(0.125,0.13,r));
  h+=0.0015*fbm(p.xyz*45.);
  return h; }
float surfH(vec4 p,int id){ if(id==1) return edgeH(p); if(id>=5) return wallH(p); return 0.; }
void wallMat(vec4 p,int room,out vec3 base,out float metal,out float rough){
  float e=edgeDist(p), r=acosh(max(-md(p,uP1),1.)), a=asinh(abs(md(p,uM[2]))), b=asinh(abs(md(p,uM[3])));
  int k=room<0?0:room-4*(room/4);
  vec3 paper= k==0? vec3(0.13,0.24,0.25) : k==1? vec3(0.30,0.10,0.09) : k==2? vec3(0.27,0.23,0.12) : vec3(0.13,0.17,0.27);
  float st=fbm(p.xyz*5.+float(room)*1.7);
  base=paper*(0.70+0.6*st);
  float dm=abs(sin(r*55.)*sin(min(a,b)*55.)); base*=1.+0.14*smoothstep(0.6,0.95,dm);
  float w=0.0035;
  float chalk=max(1.-smoothstep(w,2.*w,abs(r-0.26)), 1.-smoothstep(w,2.*w,abs(r-0.40)));
  chalk=max(chalk,(1.-smoothstep(w,2.*w,abs(a-0.09)))*step(0.18,r)*step(r,0.46));
  base=mix(base,vec3(0.80,0.82,0.78),chalk*0.35*smoothstep(0.3,0.6,fbm(p.xyz*30.)));
  base*=mix(0.5,1.,smoothstep(0.115,0.20,e));
  metal=0.; rough=0.85;
  if(e<0.118){ float gr=fbm(vec3(alongEdge(p)*60.,e*300.,1.)); base=vec3(0.20,0.11,0.055)*(0.65+0.7*gr); rough=0.42;
    if(abs(e-0.075)<0.0065){ brass(p,base,rough); metal=1.; } }
  if(r<0.16){
    if(r>0.128){ brass(p,base,rough); metal=1.; }
    else{ base=vec3(0.10,0.16,0.30)*(0.8+0.4*fbm(p.xyz*60.)); rough=0.12; metal=0.;
      float star=1.-smoothstep(0.003,0.006,min(a,b)), ring=1.-smoothstep(0.003,0.006,abs(r-0.08));
      if(max(star,ring)>0.5){ brass(p,base,rough); metal=1.; } } }
}
// ── объекты: евклидовы SDF в локальной системе координат объекта ──
mat2 rot(float a){ float c=cos(a), s=sin(a); return mat2(c,-s,s,c); }
float smin(float a,float b,float k){ float h=clamp(.5+.5*(b-a)/k,0.,1.); return mix(b,a,h)-k*h*(1.-h); }
float sdSph(vec3 p,float r){ return length(p)-r; }
float sdCaps(vec3 p,vec3 a,vec3 b,float r){ vec3 pa=p-a, ba=b-a; float h=clamp(dot(pa,ba)/dot(ba,ba),0.,1.); return length(pa-ba*h)-r; }
float sdTorZ(vec3 p,float R,float r){ vec2 q=vec2(length(p.xy)-R,p.z); return length(q)-r; }
float sdEll(vec3 p,vec3 r){ float k0=length(p/r), k1=length(p/(r*r)); return k0*(k0-1.)/max(k1,1e-6); }
float sdBox(vec3 p,vec3 b){ vec3 q=abs(p)-b; return length(max(q,0.))+min(max(q.x,max(q.y,q.z)),0.); }
float sdOct(vec3 p,float s){ p=abs(p); return (p.x+p.y+p.z-s)*0.57735027; }
float sdRCone(vec3 p,float r1,float r2,float h){ vec2 q=vec2(length(p.xz),p.y); float b=(r1-r2)/h, a=sqrt(1.-b*b), k=dot(q,vec2(-b,a));
  if(k<0.) return length(q)-r1; if(k>a*h) return length(q-vec2(0.,h))-r2; return dot(q,vec2(a,b))-r1; }
// Чертёжник: парящая мантия, капюшон, фарфоровая маска с линзой-глазом, латунный циркуль
float guardSDF(vec3 q,float sl,out int m){
  if(sl>.5){ q.xy=rot(1.1)*q.xy; }
  q.y+=0.006*sin(uTime*1.7);
  float ang=atan(q.x,q.z);
  float robe=sdRCone(q-vec3(0,-0.13,0),0.008,0.048,0.155);
  robe+=0.0028*sin(ang*7.+q.y*40.+uTime*0.8)*smoothstep(0.02,-0.12,q.y);
  float mant=sdEll(q-vec3(0,0.03,0),vec3(0.068,0.024,0.052));
  float d=smin(robe,mant,0.02); m=1;
  float hood=max(sdSph(q-vec3(0,0.082,-0.006),0.040),-(q.z-0.016));
  hood=max(hood,-sdSph(q-vec3(0,0.08,0.002),0.034));
  if(hood<d){d=hood;m=5;}
  float head=sdSph(q-vec3(0,0.078,-0.002),0.031); if(head<d){d=head;m=5;}
  float mask=sdEll(q-vec3(0,0.076,0.017),vec3(0.024,0.030,0.016)); if(mask<d){d=mask;m=3;}
  vec3 e=q-vec3(0,0.084,0.031);
  float ring=sdTorZ(e,0.011,0.0032); if(ring<d){d=ring;m=2;}
  float lens=sdEll(e,vec3(0.009,0.009,0.004)); if(lens<d){d=lens;m=4;}
  float c1=sdCaps(q,vec3(0.058,0.045,0.01),vec3(0.075,-0.11,0.03),0.0036);
  float c2=sdCaps(q,vec3(0.058,0.045,0.01),vec3(0.042,-0.11,0.045),0.0036);
  float hg=sdSph(q-vec3(0.058,0.048,0.01),0.008);
  float cmp=min(min(c1,c2),hg); if(cmp<d){d=cmp;m=2;}
  float pa=sdEll(vec3(abs(q.x),q.y,q.z)-vec3(0.05,0.042,0.0),vec3(0.022,0.012,0.026)); if(pa<d){d=pa;m=2;}
  return d;
}
float objSDF(int kind,vec3 q,float sl,out int m){
  if(kind==1) return guardSDF(q,sl,m);
  if(kind==3){ q.xz=rot(uTime*0.6)*q.xz; vec3 c=q-vec3(0,0.015,0);
    float ring=sdTorZ(c,0.040,0.0055), glass=sdEll(c,vec3(0.036,0.036,0.004));
    float h=sdCaps(q,vec3(0,-0.026,0),vec3(0,-0.075,0),0.0055), knob=sdSph(q-vec3(0,-0.08,0),0.008);
    float d=min(min(ring,h),knob); m=2; if(glass<d){d=glass;m=6;} return d; }
  if(kind==4){ q.xz=rot(sin(uTime*0.7)*0.5)*q.xz; vec3 r=q; r.z+=6.*r.x*r.x;
    float pap=sdBox(r,vec3(0.032,0.044,0.0008))-0.0005, seal=sdEll(r-vec3(0.016,-0.028,0.002),vec3(0.008,0.008,0.0025));
    if(seal<pap){m=7;return seal;} m=8; return pap*0.8; }
  if(kind==2){ float core=sdSph(q,0.011);
    vec3 r=q; r.xz=rot(uTime*1.3)*r.xz; r.yz=rot(0.6)*r.yz;
    vec3 s=q; s.xy=rot(uTime*0.9)*s.xy; s.xz=rot(1.2)*s.xz;
    float d=min(sdTorZ(r,0.026,0.0022),sdTorZ(s,0.021,0.0018)); m=2; if(core<d){d=core;m=9;} return d; }
  if(kind==7){ q.xz=rot(uTime*0.8)*q.xz; m=10; return sdOct(vec3(q.x,q.y*0.5,q.z),0.024)*0.7; }
  if(kind==5){ float ring=sdTorZ(q,0.128,0.011), disk=sdEll(q,vec3(0.122,0.122,0.002)); m=2; float d=ring; if(disk<d){d=disk;m=11;} return d; }
  m=0; return sdSph(q,0.03);
}
float sphereT(vec4 p0, vec4 v0, vec4 C, float R){
  float A=-md(p0,C), B=-md(v0,C), k=cosh(R);
  if(A<=k) return 1e9; float disc=k*k-A*A+B*B; if(disc<=0.) return 1e9;
  float u=(k-sqrt(disc))/(A+B); if(u<=1.) return 1e9; return log(u);
}
// мягкая тень от стражей на пути «точка → лампа комнаты»
float guardShadow(vec4 P, vec4 Lw){
  float dl=acosh(max(-md(P,Lw),1.)); vec4 tl=tp(Lw,P); float s=1.;
  for(int j=0;j<NO;j++){ if(j>=uNO) break; if(uOK[j].x>1.5) continue;
    vec4 C=uO[j]; float dc=acosh(max(-md(P,C),1.)); if(dc>dl||dc<0.02) continue;
    float al=asin(clamp(sinh(0.075)/sinh(dc),0.,1.)), th=acos(clamp(md(tp(C,P),tl),-1.,1.));
    s*=mix(0.25,1.,smoothstep(al*0.5,al*1.7,th)); }
  return s; }
void main(){
  vec2 uv=(2.*gl_FragCoord.xy-uRes)/uRes.y;
  vec3 dr=normalize(vec3(uv*uTanFov,1.));
  vec4 p=uCam[3], v=uCam[0]*dr.x+uCam[1]*dr.y+uCam[2]*dr.z;
  vec4 p0=p, v0=v;
  for(int i=0;i<4;i++) gA[i]=uA[i];
  // объекты: пересечение с ограничивающим шаром, затем короткий марш по SDF фигуры
  float tO=1e9, tG=1e9, tI=1e9; int iO=-1;
  for(int j=0;j<NO;j++){ if(j>=uNO) break;
    vec4 C=uO[j]; float R=uOK[j].y; float A=-md(p0,C), B=-md(v0,C), k=cosh(R);
    float disc=k*k-A*A+B*B; if(disc<=0.) continue;
    float sq=sqrt(disc), u1=(k-sq)/(A+B), u2=(k+sq)/(A+B);
    if(u2<=1.) continue;
    float t0=u1>1.? log(u1) : 0., t1=log(u2);
    int kind=int(uOK[j].x+.5); float sl=mod(uOK[j].w,2.);
    if(kind==1){ if(sl<.5) tG=min(tG,t0); } else tI=min(tI,t0);
    if(t0>=tO) continue;
    float tt=t0;
    for(int s=0;s<56;s++){
      vec4 X=cosh(tt)*p0+sinh(tt)*v0; vec3 q=vec3(md(X,uOR[j]),md(X,uOU[j]),md(X,uOD[j]));
      int m; float dd=objSDF(kind,q,sl,m);
      if(dd<2.5e-4){ if(tt<tO){tO=tt;iO=j;} break; }
      tt+=dd; if(tt>t1) break;
    }
  }
  int r0=roomKey(vec4(gA[0].w,gA[1].w,gA[2].w,gA[3].w));
  float litC= r0>=0? uLit[r0] : 0.;
  vec3 thr=vec3(1.), acc=vec3(0.); float t=0., d=0.; bool hit=false, ohit=false;
  for(int i=0;i<160;i++){
    for(int it=0;it<16;it++){
      bool any=false;
      for(int k=0;k<4;k++){
        float s=md(p,uM[k]);
        if(s>0.){
          p-=2.*s*uM[k]; v-=2.*md(v,uM[k])*uM[k];
          for(int q=0;q<4;q++) gA[q]-=2.*md(gA[q],uM[k])*uM[k];
          any=true;
          if(k==0){ int rk=roomKey(vec4(gA[0].w,gA[1].w,gA[2].w,gA[3].w)); litC= rk>=0? uLit[rk] : 0.;
            if(uGlass>.5) glassCross(p,v,t,thr,acc,LAMP,litC); }
        }
      }
      if(!any) break;
    }
    gW[0]=false; gW[1]=false; gW[2]=false;
    float d0=map(p);
    for(int q=0;q<3;q++){ float df=asinh(-md(p,uF[q])); if(df<d0+0.02) gW[q]=roomKey(nkey(uF[q]))<0; }
    d=map(p);
    if(t+d>=tO){ ohit=true; break; }
    if(d<3e-4*(1.+t)){hit=true;break;}
    float st=min(d,max(asinh(-md(p,uM[0])),0.)+1e-3);
    float sl=sinh(acosh(max(p.w,1.)));
    acc+=thr*LAMP*litC*(0.011/(0.015+sl*sl))*min(st,0.25)*exp(-t/uFog);
    adv(p,v,st); t+=st;
    if(t>14.||thr.g<0.02) break;
  }
  vec3 col=FOG; float tHit=1e9;
  int room=roomKey(vec4(gA[0].w,gA[1].w,gA[2].w,gA[3].w));
  float lit=room>=0? uLit[room] : 0.;
  if(hit){
    tHit=t;
    int id=gId; vec4 n=calcN(p,d);
    if(id==1||id>=5) n=bumpN(p,n,id,1.);
    vec4 L=tp(vec4(0,0,0,1),p); float sr=sinh(acosh(max(p.w,1.)));
    float att=1.6/(0.18+sr*sr)*lit;
    vec3 sc;
    if(id==3) sc=lampShade(n,v,LAMP,lit);
    else{
      float ao=calcAO(p,n);
      if(lit>0.&&room>=0){ vec4 P=cosh(t)*p0+sinh(t)*v0; att*=guardShadow(P,uRC[room]); }
      vec3 base; float metal=1., rough;
      if(id==1){ brass(p,base,rough); float u=alongEdge(p); float gb=abs(fract(u*13.)-0.5)/13.; base*=mix(0.40,1.,smoothstep(0.002,0.006,gb)); }
      else if(id==2){ base=vec3(0.78,0.80,0.84); rough=0.16+0.2*fbm(p.xyz*25.); }
      else wallMat(p,room,base,metal,rough);
      sc=brdf(base,metal,rough,n,v,L,p)*LAMP*att*mix(0.5,1.,ao)+ambEnv(n,v,L,LAMP,att,base,metal,rough,ao);
    }
    col=mix(FOG,sc,exp(-t/uFog));
  } else if(ohit){
    tHit=tO; t=tO;
    int j=iO; int kind=int(uOK[j].x+.5); float sl=mod(uOK[j].w,2.), litO=floor(uOK[j].w*0.5+0.01), par=uOK[j].z;
    vec4 X=cosh(tO)*p0+sinh(tO)*v0, vX=sinh(tO)*p0+cosh(tO)*v0;
    vec3 q=vec3(md(X,uOR[j]),md(X,uOU[j]),md(X,uOD[j]));
    int mm; const vec2 h=vec2(1.,-1.)*0.0006;
    vec3 nq=normalize(h.xyy*objSDF(kind,q+h.xyy,sl,mm)+h.yyx*objSDF(kind,q+h.yyx,sl,mm)+h.yxy*objSDF(kind,q+h.yxy,sl,mm)+h.xxx*objSDF(kind,q+h.xxx,sl,mm));
    objSDF(kind,q,sl,mm);
    vec4 n=tp(nq.x*uOR[j]+nq.y*uOU[j]+nq.z*uOD[j],X);
    vec4 Lc=uOC[j]; vec4 L=tp(Lc,X); float sr=sinh(acosh(max(-md(X,Lc),1.))); float att=1.6/(0.18+sr*sr)*litO;
    float f=clamp(-md(n,vX),0.,1.);
    vec3 base=vec3(0.5), emis=vec3(0.); float metal=0., rough=0.6;
    if(mm==1){ base=vec3(0.07,0.08,0.13); rough=0.8; if(sl<.5&&abs(q.y-0.012)<0.005){ brass(X,base,rough); metal=1.; } }
    else if(mm==5){ base=vec3(0.045,0.05,0.085); rough=0.85; }
    else if(mm==2){ brass(X,base,rough); metal=1.; }
    else if(mm==3){ base=vec3(0.86,0.83,0.77)*(0.9+0.15*fbm(q*300.)); rough=0.32; }
    else if(mm==4){ base=vec3(0.02); rough=0.1; emis= sl>.5? vec3(0.) : mix(vec3(1.,0.72,0.28),vec3(1.,0.12,0.05),par)*(3.5+1.5*sin(uTime*6.)*par); }
    else if(mm==6){ base=vec3(0.05,0.08,0.12); rough=0.05; emis=vec3(0.25,0.55,1.0)*(0.5+2.2*pow(1.-f,3.)); }
    else if(mm==7){ base=vec3(0.45,0.05,0.04); rough=0.35; }
    else if(mm==8){ base=vec3(0.86,0.80,0.66); rough=0.9;
      if(abs(q.x)<0.024&&q.y>-0.02&&q.y<0.036&&fract(q.y*110.)<0.3) base=vec3(0.22,0.18,0.14);
      emis=base*0.06; }
    else if(mm==9){ base=vec3(0.2); emis=vec3(1.0,0.75,0.32)*(2.5+1.2*sin(uTime*3.)); }
    else if(mm==10){ base=vec3(0.30,0.15,0.55); rough=0.12; emis=vec3(0.55,0.25,1.0)*(0.5+0.8*pow(1.-f,2.))*(1.+0.4*sin(uTime*4.)); }
    else if(mm==11){ float sw=fbm(vec3(q.xy*28.+vec2(sin(uTime*0.3),cos(uTime*0.27)),uTime*0.25));
      emis=mix(vec3(0.30,0.55,1.0),vec3(0.95,0.97,1.0),smoothstep(0.35,0.75,sw))*(0.55+0.85*par)*(0.55+0.45*smoothstep(0.122,0.03,length(q.xy))); base=vec3(0.02); }
    vec3 sc=brdf(base,metal,rough,n,vX,L,X)*LAMP*att+ambEnv(n,vX,L,LAMP,att,base,metal,rough,1.)+emis
      +vec3(0.25,0.35,0.6)*pow(1.-f,4.)*0.22;
    col=mix(FOG,sc,exp(-t/uFog));
  }
  if(uLens>0.){
    col=mix(col,vec3(dot(col,vec3(.3,.5,.2)))*vec3(0.55,0.8,1.25),0.45*uLens);
    if(tG<tHit-0.01) col=mix(col,vec3(1.,0.42,0.18),0.6*uLens);
    if(tI<tHit-0.01) col=mix(col,vec3(1.,0.85,0.40),0.5*uLens);
    if(tHit<1e8){
      vec4 P=cosh(tHit)*p0+sinh(tHit)*v0;
      for(int j=0;j<NO;j++){ if(j>=uNO) break; if(uOK[j].x>1.5||mod(uOK[j].w,2.)>.5) continue;
        float dist=acosh(max(-md(P,uO[j]),1.)); if(dist>uView||dist<0.02) continue;
        if(md(tp(P,uO[j]),uOD[j])>uCosFov) col=mix(col,vec3(1.,0.18,0.08),0.28*uLens*(1.-dist/uView)); }
    }
  }
  if(uMarkOn>.5){ float tm=sphereT(p0,v0,uMark,0.06); if(tm<tHit){ col=mix(col,vec3(0.55,0.92,1.0)*2.2,0.6); tHit=tm; } }
  fragColor=outc(acc+thr*col, tHit<1e8? tHit : 60.);
}`;
let MP=null,MPerr=null;
try{MP=program(gl,FS_MISSION);}catch(e){MPerr=e;console.error(e);}

// ───────── звук ─────────
const AU={ctx:null,on:true,drone:null,
  init(){if(this.ctx)return;try{this.ctx=new (window.AudioContext||window.webkitAudioContext)();}catch(_){return;}
    const c=this.ctx,gn=c.createGain();gn.gain.value=0.0;gn.connect(c.destination);
    const o1=c.createOscillator(),o2=c.createOscillator();o1.frequency.value=110;o2.frequency.value=165;o1.type=o2.type='sine';
    o1.connect(gn);o2.connect(gn);o1.start();o2.start();this.drone={gn,o1,o2};},
  env(dur,gain){const c=this.ctx,gn=c.createGain(),t=c.currentTime;gn.gain.setValueAtTime(0.0001,t);
    gn.gain.exponentialRampToValueAtTime(gain,t+0.015);gn.gain.exponentialRampToValueAtTime(0.0001,t+dur);gn.connect(c.destination);return gn;},
  tone(f,dur,type,gain,f2){if(!this.ctx||!this.on)return;const c=this.ctx,o=c.createOscillator();o.type=type||'sine';
    o.frequency.setValueAtTime(f,c.currentTime);if(f2)o.frequency.exponentialRampToValueAtTime(f2,c.currentTime+dur);
    o.connect(this.env(dur,gain||0.08));o.start();o.stop(c.currentTime+dur+0.05);},
  noise(dur,f1,f2,gain){if(!this.ctx||!this.on)return;const c=this.ctx,n=Math.floor(c.sampleRate*dur),b=c.createBuffer(1,n,c.sampleRate),a=b.getChannelData(0);
    for(let i=0;i<n;i++)a[i]=Math.random()*2-1;const s=c.createBufferSource();s.buffer=b;const bp=c.createBiquadFilter();bp.type='bandpass';bp.Q.value=2;
    bp.frequency.setValueAtTime(f1,c.currentTime);bp.frequency.exponentialRampToValueAtTime(f2,c.currentTime+dur);s.connect(bp);bp.connect(this.env(dur,gain||0.2));s.start();},
  blink(){this.noise(0.35,2400,260,0.25);this.tone(660,0.25,'sine',0.04,220);},
  pick(){this.tone(880,0.5,'sine',0.07);setTimeout(()=>this.tone(1320,0.6,'sine',0.05),70);},
  alert(){this.tone(220,0.5,'sawtooth',0.04);this.tone(233,0.5,'sawtooth',0.04);},
  sleep(){this.tone(110,0.4,'triangle',0.12,55);},
  fail(){this.tone(330,1.2,'sawtooth',0.05,110);this.tone(349,1.2,'sawtooth',0.04,98);},
  win(){[523,659,784,1047].forEach((f,i)=>setTimeout(()=>this.tone(f,0.9,'sine',0.05),i*120));},
  lamp(){this.tone(1800,0.08,'square',0.02,900);},
  setDrone(alert,active){if(!this.drone)return;const t=this.ctx.currentTime;
    this.drone.gn.gain.setTargetAtTime(active&&this.on?0.018:0,t,0.3);
    // чистая квинта «Машин Прямизны» расстраивается вместе с тревогой
    this.drone.o2.frequency.setTargetAtTime(165*(1+0.045*alert),t,0.2);},
};

// ───────── интерфейс ─────────
const css=`
#mhud{position:fixed;inset:0;pointer-events:none;display:none;font-family:var(--body)}
#mhud.on{display:block}
#mhud>*{pointer-events:none}
#mobj{position:absolute;left:calc(16px + env(safe-area-inset-left,0px));top:calc(14px + env(safe-area-inset-top,0px));max-width:min(420px,calc(100vw - 32px));text-shadow:0 1px 8px #000}
#mobj .ch{font-size:11px;letter-spacing:.14em;text-transform:uppercase;color:var(--brass)}
#mobj .rn{font-family:var(--display);font-size:28px;line-height:1.05;margin:2px 0 8px}
#mobj ul{list-style:none;margin:0;padding:0;display:flex;flex-direction:column;gap:3px;font-size:13px}
#mobj li::before{content:"◇ ";color:var(--brass)}
#mobj li.done{color:var(--muted);text-decoration:line-through}
#mobj li.done::before{content:"◆ "}
#mobj li.locked{color:var(--muted);opacity:.6}
#mbar{position:absolute;left:calc(16px + env(safe-area-inset-left,0px));bottom:calc(16px + env(safe-area-inset-bottom,0px));display:flex;flex-direction:column;gap:6px;background:var(--panel);padding:4px 6px;min-width:220px}
#mbar .lbl{display:flex;justify-content:space-between;font-size:11px;letter-spacing:.1em;text-transform:uppercase;color:var(--muted)}
#mbar .track{height:6px;background:rgba(255,255,255,.08);border-radius:3px;overflow:hidden}
#mbar .fill{height:100%;background:linear-gradient(90deg,#4b36a8,#8f74ff 70%,#d9ccff);width:50%;box-shadow:0 0 10px #8f74ff}
#mbar .ab{display:flex;gap:10px;font-size:12px;color:var(--fg)}
#mbar .ab span{opacity:.95}#mbar .ab span.off{opacity:.35}
#mbar kbd{font:500 10px var(--mono);border:1px solid var(--line);border-radius:2px;padding:1px 4px;margin-right:4px;color:var(--brass)}
#mprompt{position:absolute;left:50%;top:calc(50% + 34px);transform:translateX(-50%);font-size:14px;color:var(--fg);background:rgba(12,14,28,.7);border:1px solid var(--line);border-radius:3px;padding:6px 12px;display:none;white-space:nowrap}
#mprompt b{color:var(--brass);font-family:var(--mono);font-weight:500}
#msub{position:absolute;left:50%;transform:translateX(-50%);bottom:calc(92px + env(safe-area-inset-bottom,0px));width:min(700px,calc(100vw - 32px));text-align:center;font-family:var(--serif);font-style:italic;font-size:18px;line-height:1.45;color:var(--fg);text-shadow:0 1px 6px #000,0 0 18px #000;transition:opacity .5s}
#msub .who{color:var(--brass);font:600 11px var(--body);font-style:normal;letter-spacing:.16em;text-transform:uppercase;display:block;margin-bottom:2px}
#mtitle{position:absolute;left:50%;top:22%;transform:translateX(-50%);font-family:var(--display);font-size:52px;letter-spacing:.01em;color:var(--fg);text-shadow:0 2px 20px #000;opacity:0;transition:opacity .8s;text-align:center;white-space:nowrap}
#mtitle small{display:block;font-family:var(--body);font-size:11px;letter-spacing:.3em;text-transform:uppercase;color:var(--brass);margin-bottom:4px}
#mtitle i{display:block;margin:8px auto 0;width:220px;height:9px;background:linear-gradient(90deg,transparent,var(--brass) 30%,transparent 48%,transparent 52%,var(--brass) 70%,transparent) center/100% 1px no-repeat,radial-gradient(circle,var(--brass) 0 3px,transparent 3.5px) center/9px 9px no-repeat}
#mplaque{position:absolute;right:calc(16px + env(safe-area-inset-right,0px));top:calc(14px + env(safe-area-inset-top,0px));width:min(380px,calc(100vw - 32px));background:radial-gradient(ellipse at top,#1b2038,#0d1020);padding:8px 10px;display:none;line-height:1.55}
#mplaque h4{margin:0 0 6px;font-family:var(--display);font-size:27px;color:var(--brass);font-weight:400}
#mplaque p{margin:0;font-family:var(--serif);font-size:15px}
#mplaque .k{margin-top:8px;font-size:11px;color:var(--muted)}
#mind .gi{position:absolute;transform:translate(-50%,-100%);width:22px;height:13px;border-radius:50%;border:2px solid #f2c063;background:transparent;overflow:hidden;box-shadow:0 0 6px #000}
#mind .gi i{position:absolute;left:0;bottom:0;width:100%;background:#f2c063}
#mind .gi.chase{border-color:#ff3b26}#mind .gi.chase i{background:#ff3b26}
#mflash{position:fixed;inset:0;pointer-events:none;background:radial-gradient(circle,rgba(160,220,255,.0) 20%,rgba(160,220,255,.55));opacity:0;transition:opacity .35s}
#mlensv{position:fixed;inset:0;pointer-events:none;background:radial-gradient(ellipse at center,rgba(60,120,255,0) 45%,rgba(40,90,220,.35));opacity:0;transition:opacity .25s}
#mscreen{position:fixed;inset:0;display:none;align-items:center;justify-content:center;padding:16px;background:rgba(6,8,16,.82);backdrop-filter:blur(6px);-webkit-backdrop-filter:blur(6px);pointer-events:auto;z-index:5}
#mscreen.on{display:flex}
#mscreen .card{width:min(640px,100%);max-height:calc(100vh - 32px);overflow:auto;background:radial-gradient(ellipse at top,#1c2140,#0c0f1c 70%);padding:16px 22px;line-height:1.55;box-shadow:0 20px 80px rgba(0,0,0,.6)}
#mscreen .crest{display:flex;flex-direction:column;align-items:center;text-align:center;margin:4px 0 14px}
#mscreen .crest svg{width:96px;height:96px;filter:drop-shadow(0 0 14px rgba(214,163,90,.35))}
#mscreen .wordmark{font-family:var(--display);font-size:50px;line-height:1;letter-spacing:.06em;text-transform:uppercase;margin-top:10px;background:linear-gradient(180deg,#f6dfab,#d6a35a 55%,#8a5f2c);-webkit-background-clip:text;background-clip:text;color:transparent;filter:drop-shadow(0 2px 0 rgba(0,0,0,.6))}
#mscreen .crest .ch{margin-top:8px}
#mscreen .ch{font-size:11px;letter-spacing:.16em;text-transform:uppercase;color:var(--brass)}
#mscreen h2{font-family:var(--display);font-size:44px;line-height:1.05;margin:4px 0 12px;font-weight:400}
#mscreen .crest h2{margin:2px 0 0}
#mscreen p{margin:0 0 10px;font-family:var(--serif);font-size:16px}
#mscreen .q{font-family:var(--serif);font-style:italic;font-size:17px;color:var(--fg);border-left:2px solid var(--brass);padding-left:12px;margin:12px 0}
#mscreen .ctrls{display:grid;grid-template-columns:auto 1fr;gap:4px 14px;font-size:13px;color:var(--muted);margin:12px 0}
#mscreen .ctrls b{font-family:var(--mono);font-weight:500;color:var(--brass)}
#mscreen .stats{display:grid;grid-template-columns:1fr auto;gap:4px 16px;font-size:14px;margin:12px 0}
#mscreen .stats span:nth-child(2n){font-family:var(--mono);text-align:right}
#mscreen .rank{font-family:var(--display);font-size:30px;color:var(--brass)}
#mscreen .row{margin-top:16px}
#mscreen .btn{letter-spacing:.06em;text-transform:uppercase;font-size:11.5px;padding:10px 14px;margin:0 6px 6px 0}
#mscreen .btn.main{background:linear-gradient(180deg,#f0c983,#c08a45);color:#1a1206;border-color:#f0c983;font-weight:600;box-shadow:0 0 18px rgba(214,163,90,.35)}
#mscreen details{margin-top:6px;font-size:13px}#mscreen summary{cursor:pointer;color:var(--brass)}
#mmap{position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);width:min(520px,calc(100vw - 32px));aspect-ratio:1;background:rgba(8,12,26,.92);border:1px solid var(--brass);border-radius:50%;display:none;pointer-events:none;z-index:4}
#mmap.on{display:block}
#mtouch{position:absolute;right:calc(20px + env(safe-area-inset-right,0px));bottom:calc(150px + env(safe-area-inset-bottom,0px));display:none;flex-direction:column;gap:10px;pointer-events:auto}
#mtouch button{width:56px;height:56px;border-radius:50%;border:1px solid var(--line);background:rgba(12,14,28,.65);color:var(--fg);font-size:12px;touch-action:none}
#mpause{position:absolute;right:calc(16px + env(safe-area-inset-right,0px));top:calc(14px + env(safe-area-inset-top,0px));pointer-events:auto;display:none}
#mtoast{position:absolute;left:50%;top:calc(14px + env(safe-area-inset-top,0px));transform:translateX(-50%);font-size:13px;background:var(--panel);border:1px solid var(--line);border-radius:3px;padding:6px 12px;opacity:0;transition:opacity .4s}
@media (pointer:coarse){#mtouch{display:flex}#mpause{display:block}#mbar{bottom:calc(150px + env(safe-area-inset-bottom,0px))}}
@media (max-width:760px){#mobj .rn{font-size:18px}#mtitle{font-size:26px}#msub{font-size:13px;bottom:calc(170px + env(safe-area-inset-bottom,0px))}#mplaque{top:auto;bottom:calc(230px + env(safe-area-inset-bottom,0px))}#mscreen h2{font-size:28px}}
`;
const st=document.createElement('style');st.textContent=css;document.head.appendChild(st);
const hudEl=document.createElement('div');hudEl.id='mhud';
hudEl.innerHTML=`<div id="mlensv"></div><div id="mind"></div>
<div id="mobj"><div class="ch">Глава 1 · Архив лишних точек</div><div class="rn" id="mroom"></div><ul id="mlist"></ul></div>
<div id="mbar" class="framed"><div class="lbl"><span>Дефект</span><span id="mmana" class="mono"></span></div><div class="track"><div class="fill" id="mfill"></div></div>
<div class="ab"><span id="ab-blink"><kbd>ПКМ</kbd>Рывок</span><span id="ab-lens" class="off"><kbd>V</kbd>Линза</span><span><kbd>F</kbd>Действие</span></div></div>
<div id="mprompt"></div><div id="msub"></div><div id="mtitle"></div><div id="mtoast"></div>
<div id="mplaque" class="framed"><h4 id="mpl-t"></h4><p id="mpl-x"></p><div class="k">Лемма записана в журнал (Esc → Леммы)</div></div>
<div id="mtouch"><button id="mt-blink">Рывок</button><button id="mt-lens">Линза</button><button id="mt-act">F</button></div>
<button class="btn" id="mpause">II</button>`;
document.getElementById('ui').appendChild(hudEl);
const flash=document.createElement('div');flash.id='mflash';document.body.appendChild(flash);
const screen=document.createElement('div');screen.id='mscreen';document.body.appendChild(screen);
const mapC=document.createElement('canvas');mapC.id='mmap';mapC.width=1040;mapC.height=1040;document.body.appendChild(mapC);
const $=id=>document.getElementById(id);

// ───────── состояние миссии ─────────
let S=null,active=false,aiming=false,mapOn=false;
const SAVE_KEY='p5-ch1-save';
function fresh(){
  const s2=RI('s2'),hub=RI('hub');const c=ROOMS[s2].c;
  const start=advancePose(c,perpAt(c,dirTo(c,ROOMS[hub].c)),0.35).p;
  const cam={M:frameAt(start,dirTo(start,faceCenter(s2,hub))),G:I4(),par:0,cross:0};foldRooms(cam,g);
  return {c:cam,mana:0.5,hasLens:false,lensOn:false,got:{},lit:ROOMS.map(r=>r.lit0),
    guards:GUARD_SPEC.map((sp,i)=>new Guard(sp,i)),visited:[s2],room:s2,time:0,
    stats:{alerts:0,sleeps:0,bodies:0,blinks:0,seen:0},flags:{},paused:false,over:false,subs:[],plaqueT:0};
}
function serialize(){return JSON.stringify({v:1,c:S.c,mana:S.mana,hasLens:S.hasLens,got:S.got,lit:S.lit,
  guards:S.guards.map(x=>x.toJSON()),visited:S.visited,time:S.time,stats:S.stats,flags:S.flags});}
function deserialize(str){const o=JSON.parse(str);const s=fresh();
  Object.assign(s,{c:o.c,mana:o.mana,hasLens:o.hasLens,got:o.got,lit:o.lit,visited:o.visited,time:o.time,stats:o.stats,flags:o.flags});
  o.guards.forEach((gj,i)=>{const G=s.guards[i];Object.assign(G,gj);G.scan=null;if(G.state==='chase'){G.state='search';G.timer=0;}G.alert=Math.min(G.alert,0.6);});
  s.room=-1;return s;}
function save(){try{localStorage.setItem(SAVE_KEY,serialize());toast('Сохранено');}catch(_){toast('Сохранить не удалось');}}
function hasSave(){try{return !!localStorage.getItem(SAVE_KEY);}catch(_){return false;}}
function load(){try{const s=localStorage.getItem(SAVE_KEY);if(!s)return false;S=deserialize(s);ui.obj();toast('Загружено');return true;}catch(e){console.error(e);return false;}}

// ───────── реплики ─────────
function say(who,text,dur){S.subs.push({who,text,dur:dur??Math.max(4,text.length*0.055)});}
function once(flag,fn){if(!S.flags[flag]){S.flags[flag]=1;fn();}}
let toastT=0;function toast(t){const e=$('mtoast');e.textContent=t;e.style.opacity=1;toastT=performance.now()+1600;}

// ───────── игровой цикл ─────────
const PR_=0.07,BLINK_MAX=1.7,BLINK_COST=0.25,REGEN_CAP=0.5;
const pos=()=>normalizePoint(apply(S.c.G,col(S.c.M,3)));
const basis=k=>apply(S.c.G,col(S.c.M,k));
function blinkTarget(){const p=pos(),f=tangent(basis(2),p);
  const free=raymarchObstacles(p,f,BLINK_MAX+0.2,x=>sdfWorld(x,0.06),0.15);
  const s=clamp(Math.min(free,BLINK_MAX+0.2)-0.16,0,BLINK_MAX);return {s,pt:advancePose(p,f,s).p};}
function doBlink(){const b=blinkTarget();if(b.s<0.12)return;
  if(S.mana<BLINK_COST){toast('Не хватает дефекта');return;}
  S.mana-=BLINK_COST;boostLocal(S.c.M,2,b.s);gs(S.c.M);foldRooms(S.c,g);S.stats.blinks++;
  flash.style.transition='none';flash.style.opacity=1;requestAnimationFrame(()=>{flash.style.transition='opacity .35s';flash.style.opacity=0;});
  AU.blink();noise(b.pt,0.45);}
function noise(at,loud){for(const G of S.guards){if(G.sleep)continue;const d=hyperbolicDistance(G.pos,at),sh=Math.sinh(d),h=loud/(1+sh*sh);
  if(h>0.08){G.alert=clamp(G.alert+0.6*h,0,1);G.heard=at.slice();if(G.state==='patrol'&&G.alert>0.15){G.state='suspect';G.timer=0;G.goal=at.slice();G.scan=null;}}}}
function collide(prev){
  for(let it=0;it<3;it++){const p=pos(),d=sdfWorld(p,0.06);if(d>=PR_)return;
    const gr=[0,1,2].map(k=>{const q=advancePose(p,tangent(basis(k),p),0.01).p;return (sdfWorld(q,0.06)-d)/0.01;});
    for(let k=0;k<3;k++)boostLocal(S.c.M,k,gr[k]*(PR_-d)*1.05);gs(S.c.M);foldRooms(S.c,g);}
  if(sdfWorld(pos(),0.06)<PR_*0.5){S.c.M=prev.M;S.c.G=prev.G;S.c.par=prev.par;S.c.cross=prev.cross;}}
function interactTarget(){const p=pos();
  for(const G of S.guards){if(G.sleep||G.state==='chase')continue;const d=hyperbolicDistance(p,G.pos);
    if(d<0.45){const ang=Math.acos(clamp(md(G.dir,dirTo(G.pos,p)),-1,1));if(ang>FOV/2*0.85||G.alert<0.35)return {type:'guard',G,label:'Усыпить стража'};}}
  for(const it of ITEMS){if(S.got[it.id]||it.kind===5)continue;if(hyperbolicDistance(p,it.pos)<0.3)
    return {type:'item',it,label:it.kind===2?'Прочесть лемму':it.kind===7?'Взять крупицу дефекта':'Взять: '+it.name};}
  const r=S.room;if(r>=0&&hyperbolicDistance(p,ROOMS[r].c)<0.36)return {type:'lamp',r,label:S.lit[r]?'Погасить лампу':'Зажечь лампу'};
  return null;}
function interact(){const t=interactTarget();if(!t)return;
  if(t.type==='guard'){t.G.sleep=true;t.G.alert=0;t.G.state='sleep';S.stats.sleeps++;AU.sleep();
    once('sleep1',()=>say('Николай','Он проснётся к утру и ничего не вспомнит. Но если спящего найдут, Архив поднимут на ноги — не оставляй его на виду.'));}
  else if(t.type==='item'){const it=t.it;S.got[it.id]=1;AU.pick();
    if(it.kind===2){showPlaque(LEMMAS[it.lemma]);}
    else if(it.kind===7){S.mana=Math.min(1,S.mana+0.5);toast('Дефект +0,5');}
    else if(it.id==='lens'){S.hasLens=true;ui.obj();
      say('Николай','Теперь смотри. Прямизна — лишь занавес. Линза показывает стражей сквозь камень и то, куда они смотрят. Держи [V].',7);save();}
    else if(it.id==='rec'){ui.obj();showPlaque({t:'Перепись · лист 281',x:'«Житель без дома и имени. Положение — точка вне прямой. Пометка Церкви: через неё проходят две параллели. Вычеркнуть, все списки изъять».'});
      say('Николай','Вычеркнутый жив, пока о нём помнит хоть одна запись. Теперь — к Окну на Абсолют, через Коридор окна за Атриумом.',7);save();}}
  else if(t.type==='lamp'){S.lit[t.r]=!S.lit[t.r];AU.lamp();}}
function showPlaque(L){$('mpl-t').textContent=L.t;$('mpl-x').innerHTML=L.x;$('mplaque').style.display='block';S.plaqueT=11;}

function update(dt){
  const c=S.c;S.time+=dt;
  const prev={M:c.M.slice(),G:c.G.slice(),par:c.par,cross:c.cross};
  const run=keys.has('ShiftLeft')||keys.has('ShiftRight');
  const sp=(run?1.15:0.45)*dt;
  const f=(keys.has('KeyW')||keys.has('ArrowUp')?1:0)-(keys.has('KeyS')||keys.has('ArrowDown')?1:0)+joy[1];
  const s=(keys.has('KeyD')?1:0)-(keys.has('KeyA')?1:0)+joy[0];
  const u=(keys.has('Space')?1:0)-(keys.has('KeyC')||keys.has('ControlLeft')?1:0)+vbtn;
  const turn=(keys.has('ArrowRight')?1:0)-(keys.has('ArrowLeft')?1:0);
  const roll=(keys.has('KeyE')?1:0)-(keys.has('KeyQ')?1:0);
  const lx=look[0]*0.0026+turn*1.6*dt,ly=look[1]*0.0026;look=[0,0];
  if(lx)rotLocal(c.M,2,0,lx);if(ly)rotLocal(c.M,2,1,-ly);if(roll)rotLocal(c.M,0,1,roll*1.2*dt);
  const movingAmt=Math.min(1,Math.hypot(f,s,u));
  if(f)boostLocal(c.M,2,f*sp);if(s)boostLocal(c.M,0,s*sp);if(u)boostLocal(c.M,1,u*sp);
  gs(c.M);foldRooms(c,g);
  if(movingAmt)collide(prev);
  const p=pos(),r=roomOfPoint(p);
  if(r>=0&&r!==S.room){S.room=r;if(!S.visited.includes(r)){S.visited.push(r);roomTitle(ROOMS[r].name);}$('mroom').textContent=ROOMS[r].name;
    if(!S.lit[r])once('dark',()=>say('Николай','Во тьме тебя почти не видно. Лампу можно погасить и самой — подойди к ней и нажми [F].'));}
  // дефект и Линза
  if(S.lensOn){S.mana-=0.05*dt;if(S.mana<=0){S.mana=0;S.lensOn=false;}}
  else if(S.mana<REGEN_CAP)S.mana=Math.min(REGEN_CAP,S.mana+0.03*dt);
  if(run&&movingAmt>0.1)noise(p,0.9*dt*6);
  // стражи
  const lightF=r>=0&&S.lit[r]?1:0.28,motionF=movingAmt>0.1?(run?1.4:1):0.6;
  let maxA=0;
  for(const G of S.guards){if(G.sleep)continue;updateGuard(G,dt,p,lightF,motionF);maxA=Math.max(maxA,G.alert);}
  S.maxA=maxA;
  // выход
  const ex=ITEMS.find(i=>i.kind===5);
  if(hyperbolicDistance(p,ex.pos)<0.22){if(S.got.lens&&S.got.rec)finish();
    else once('early',()=>say('Николай','Ещё рано. Линза и лист 281 должны быть у тебя.'));}
  else if(S.flags.early&&hyperbolicDistance(p,ex.pos)>0.6)S.flags.early=0;
  // реплики
  if(S.subs.length){const sub=S.subs[0];if(!sub.shown){sub.shown=1;$('msub').innerHTML=`<span class="who">${sub.who}</span>${sub.text}`;$('msub').style.opacity=1;}
    sub.dur-=dt;if(sub.dur<=0){S.subs.shift();$('msub').style.opacity=0;}}
  if(S.plaqueT>0){S.plaqueT-=dt;if(S.plaqueT<=0)$('mplaque').style.display='none';}
}
function updateGuard(G,dt,p,lightF,motionF){
  const sc=G.perceive(p,lightF,motionF);G.sees=sc;
  if(sc>0){G.alert=clamp(G.alert+dt*RATE*sc,0,1);G.lastSeen=p.slice();G.seenAgo=0;}
  else{G.seenAgo+=dt;G.alert=clamp(G.alert-dt*(G.state==='chase'?0.10:0.22),0,1);}
  // спящие товарищи
  for(const H of S.guards)if(H!==G&&H.sleep&&!H.found&&G.sees_(H.pos,2.6)){H.found=true;S.stats.bodies++;
    G.alert=Math.max(G.alert,0.75);G.state='search';G.goal=H.pos.slice();G.timer=0;G.scan=null;AU.alert();toast(G.name+' нашёл спящего');}
  if(G.alert>=1&&G.state!=='chase'){G.state='chase';G.scan=null;S.stats.alerts++;AU.alert();
    once('seen1',()=>say('Николай','Тебя заметили! Уходи из света, разорви линию взгляда — и он потеряет след.'));
    for(const H of S.guards)if(H!==G&&!H.sleep&&hyperbolicDistance(H.pos,G.pos)<3){H.alert=Math.max(H.alert,0.7);if(H.state!=='chase'){H.state='search';H.goal=p.slice();H.timer=0;H.scan=null;}}}
  const dP=hyperbolicDistance(G.pos,p);
  switch(G.state){
    case 'patrol':{
      if(G.alert>0.3){G.state='suspect';G.timer=0;G.goal=(G.lastSeen||G.heard||p).slice();G.scan=null;break;}
      if(G.wait>0){G.wait-=dt;G.look(dt);if(G.wait<=0)G.scan=null;break;}
      const w=G.route[G.wp];
      if(G.moveTo(w.p,0.28,dt)){G.wait=w.wait;G.wp=(G.wp+1)%G.route.length;}
      const gr=roomOfPoint(G.pos);if(gr>=0&&ROOMS[gr].lit0&&!S.lit[gr]&&hyperbolicDistance(G.pos,ROOMS[gr].c)<0.55){S.lit[gr]=true;G.alert=Math.max(G.alert,0.2);AU.lamp();}
      break;}
    case 'suspect':{G.timer+=dt;if(G.goal)G.turn(dirTo(G.pos,G.goal),dt,3);
      if(G.timer>0.9&&G.goal&&hyperbolicDistance(G.pos,G.goal)>0.3)G.moveTo(G.nav(G.goal),0.22,dt);
      if(G.sees>0&&G.lastSeen)G.goal=G.lastSeen.slice();
      if(G.alert<0.12&&G.timer>3){G.state='return';G.scan=null;}break;}
    case 'chase':{const tg=G.seenAgo<0.2?p:(G.lastSeen||p);G.moveTo(G.nav(tg),0.62,dt);
      if(dP<CATCH)caught(G);
      if(G.seenAgo>3.2){G.state='search';G.goal=(G.lastSeen||p).slice();G.timer=0;G.scan=null;G.alert=Math.min(G.alert,0.85);}break;}
    case 'search':{G.timer+=dt;if(G.goal&&hyperbolicDistance(G.pos,G.goal)>0.25&&G.timer<12)G.moveTo(G.nav(G.goal),0.40,dt);else G.look(dt);
      if(G.timer>13||(G.alert<0.1&&G.timer>6)){G.state='return';G.scan=null;}break;}
    case 'return':{const w=G.route[G.wp];if(G.moveTo(G.nav(w.p),0.30,dt))G.state='patrol';if(G.alert>0.3){G.state='suspect';G.timer=0;G.goal=(G.lastSeen||p).slice();}break;}
  }
}
function caught(G){if(S.over)return;S.over=true;AU.fail();
  screenShow(`<div class="ch">Глава 1 · провал</div><h2>Вас схватили</h2><p>${G.name} держит вас за плечо. Циркуляторы Церкви не прощают дефекта.</p>
  <div class="q">«Нет ни одной области математики, как бы абстрактна она ни была, которая когда-нибудь не окажется применимой к явлениям действительного мира». — Н. И. Лобачевский</div>
  <div class="row">${hasSave()?'<button class="btn main" data-a="load">Загрузить сохранение</button>':''}<button class="btn${hasSave()?'':' main'}" data-a="restart">Начать заново</button><button class="btn" data-a="quit">Выйти в прогулку</button></div>`);}
function finish(){if(S.over)return;S.over=true;AU.win();
  const lem=ITEMS.filter(i=>i.kind===2&&S.got[i.id]).length,st=S.stats;
  const rank=st.alerts===0&&st.sleeps===0?'Призрак: вас не видели, никто не усыплён':st.alerts===0?'Тень: ни одной тревоги':st.alerts<3?'Свидетели есть, но вы ушли':'Архив гудит, как улей';
  const tm=Math.floor(S.time/60)+':'+String(Math.floor(S.time%60)).padStart(2,'0');
  try{localStorage.removeItem(SAVE_KEY);}catch(_){}
  screenShow(`<div class="ch">Глава 1 · пройдена</div><h2>Окно на Абсолют</h2>
  <p>Вера выходит туда, где у мира нет края. Лист 281 и Линза — у неё. Где-то за Прямизной ждёт Тюрьма-додекаэдр.</p>
  <div class="rank">${rank}</div>
  <div class="stats"><span>Время</span><span>${tm}</span><span>Тревоги</span><span>${st.alerts}</span><span>Усыплено стражей</span><span>${st.sleeps}</span>
  <span>Найдено спящих</span><span>${st.bodies}</span><span>Рывков</span><span>${st.blinks}</span><span>Леммы</span><span>${lem} / ${LEMMAS.length}</span></div>
  <p style="color:var(--muted);font-size:13px">Это вертикальный срез вехи 1. Дальше по концепту — Глава 2 «Тюрьма-додекаэдр».</p>
  <div class="row"><button class="btn main" data-a="restart">Сыграть ещё раз</button><button class="btn" data-a="quit">Выйти в прогулку</button></div>`);}
function roomTitle(n){const e=$('mtitle');e.innerHTML=`<small>Архив</small>${n}<i></i>`;e.style.opacity=1;clearTimeout(roomTitle.t);roomTitle.t=setTimeout(()=>e.style.opacity=0,2200);}

// ───────── рендер ─────────
const BOUND={1:0.16,2:0.04,3:0.095,4:0.07,5:0.15,7:0.05};
const ITEM_FR=ITEMS.map(it=>{const rc=ROOMS[RI(it.room)].c;
  const look=it.kind===5?ROOMS[RI('c1')].c:rc;return {F:frameAt(it.pos,dirTo(it.pos,look)),room:RI(it.room)};});
function render(now){
  const SC=sceneBegin();
  if(!MP){sceneEnd(SC,now);return;}const P=MP;gl.useProgram(P.pr);const L=P.loc,c=S.c,Gi=linv(c.G);
  const f1=(n,v)=>{if(L[n]!=null)gl.uniform1f(L[n],v);},i1=(n,v)=>{if(L[n]!=null)gl.uniform1i(L[n],v);},
    f4=(n,v)=>{if(L[n]!=null)gl.uniform4fv(L[n],v);};
  gl.uniform2fv(L.uRes,[SC.sw,SC.sh]);gl.uniformMatrix4fv(L.uCam,false,c.M);f1('uDirect',SC.post?0:1);
  f1('uTanFov',fovTan());f1('uFog',6.5);f1('uGlass',1);f1('uTube',0.04);f1('uBall',0.085);f1('uCamPar',c.par);
  f4('uM',g.M.flat());f4('uE1',g.E1);f4('uE2',g.E2);f4('uV',g.V);f4('uF',FACES.slice(0,3).flat());f4('uP1',g.P1);
  f4('uA',ANCH.map(a=>apply(Gi,a)).flat());
  f4('uK',ROOMS.map(r=>r.key).flat());f4('uRC',ROOMS.map(r=>apply(Gi,r.c)).flat());
  if(L.uLit!=null)gl.uniform1fv(L.uLit,S.lit.map(x=>x?1:0));i1('uNK',ROOMS.length);
  const O_=[],R_=[],U_=[],D_=[],K_=[],C_=[];
  const push=(pos,F,kind,par,sl,room)=>{O_.push(...apply(Gi,pos));R_.push(...apply(Gi,col(F,0)));U_.push(...apply(Gi,col(F,1)));D_.push(...apply(Gi,col(F,2)));
    const lit=room>=0&&S.lit[room]?1:0;K_.push(kind,BOUND[kind],par,(sl?1:0)+2*lit);C_.push(...apply(Gi,room>=0?ROOMS[room].c:pos));};
  for(const G of S.guards){const F=frameAt(G.pos,G.dir);push(G.pos,F,1,G.state==='chase'?1:G.alert*0.6,G.sleep,roomOfPoint(G.pos));}
  ITEMS.forEach((it,i)=>{if(S.got[it.id])return;const on=it.kind===5?(S.got.lens&&S.got.rec?1:0):0;push(it.pos,ITEM_FR[i].F,it.kind,on,false,ITEM_FR[i].room);});
  f4('uO',O_);f4('uOR',R_);f4('uOU',U_);f4('uOD',D_);f4('uOK',K_);f4('uOC',C_);i1('uNO',O_.length/4);
  f1('uLens',S.lensOn?1:0);f1('uTime',now/1000);f1('uCosFov',Math.cos(FOV/2));f1('uView',VIEW);
  if(aiming&&!S.over&&!S.paused){const b=blinkTarget();f4('uMark',apply(Gi,b.pt));f1('uMarkOn',b.s>0.12?1:0);}else f1('uMarkOn',0);
  gl.drawArrays(gl.TRIANGLES,0,3);
  if(typeof POST!=='undefined')POST.cfg.expo=1;
  sceneEnd(SC,now);
}
const ui={
  obj(){const L=$('mlist');if(!L)return;const done=S.got.lens&&S.got.rec;
    L.innerHTML=`<li class="${S.got.lens?'done':''}">Найти Линзу Абсолюта — Хранилище чертежей</li>
      <li class="${S.got.rec?'done':''}">Найти лист о 281-м жителе — Зал переписи</li>
      <li class="${done?'':'locked'}">Уйти через Окно на Абсолют</li>`;
    $('ab-lens').classList.toggle('off',!S.hasLens);},
};
function hud(){
  $('mmana').textContent=fmt(S.mana);$('mfill').style.width=(S.mana*100).toFixed(1)+'%';
  $('ab-blink').classList.toggle('off',S.mana<BLINK_COST);
  const t=S.over||S.paused?null:interactTarget();const pe=$('mprompt');
  if(t){pe.innerHTML=`<b>[F]</b> ${t.label}`;pe.style.display='block';}else pe.style.display='none';
  $('mlensv').style.opacity=S.lensOn?1:0;
  document.getElementById('danger').style.opacity=(S.over?0:Math.min(1,S.maxA||0)*0.85).toFixed(3);
  if(toastT&&performance.now()>toastT){$('mtoast').style.opacity=0;toastT=0;}
  AU.setDrone(S.maxA||0,!S.over&&!S.paused);
  // индикаторы над стражами
  const box=$('mind');while(box.children.length<S.guards.length){const e=document.createElement('div');e.className='gi';e.innerHTML='<i></i>';box.appendChild(e);}
  const p=pos(),b=[0,1,2].map(basis),tf=fovTan(),W=innerWidth,H=innerHeight;
  S.guards.forEach((G,i)=>{const e=box.children[i];
    if(G.sleep||S.over||(G.alert<0.04&&G.state!=='chase')){e.style.display='none';return;}
    const d=hyperbolicDistance(p,G.pos),dir=dirTo(p,G.pos),x=md(dir,b[0]),y=md(dir,b[1]),z=md(dir,b[2]);
    if(z<0.05){e.style.display='none';return;}
    const ar=Math.asin(clamp(Math.sinh(0.09)/Math.sinh(Math.max(d,0.1)),0,1));
    const X=W/2+(x/z)/tf*H/2,Y=H/2-(y/z)/tf*H/2-Math.tan(ar)/tf*H/2-8;
    e.style.display='block';e.style.left=X+'px';e.style.top=Y+'px';
    e.classList.toggle('chase',G.state==='chase');e.firstChild.style.height=(G.state==='chase'?100:G.alert*100).toFixed(0)+'%';});
  if(mapOn)drawMap();
}
function drawMap(){const x=mapC.getContext('2d'),W=mapC.width,R=W*0.46;x.clearRect(0,0,W,W);
  const pr=k=>{const a=k[0]/k[3],b=k[1]/k[3],cc=k[2]/k[3];return [W/2+R*(0.82*a-0.5*cc),W/2-R*(0.85*b+0.28*a+0.25*cc)];};
  x.lineWidth=3;x.strokeStyle='rgba(214,163,90,.55)';
  for(const i of S.visited)for(const j of ROOMS[i].nb)if(S.visited.includes(j)&&i<j){const a=pr(ROOMS[i].c),b=pr(ROOMS[j].c);x.beginPath();x.moveTo(...a);x.lineTo(...b);x.stroke();}
  x.font='500 26px IBM Plex Sans, sans-serif';x.textAlign='center';
  const known=new Set(S.visited);for(const i of S.visited)for(const j of ROOMS[i].nb)known.add(j);
  for(const i of known){const [X,Y]=pr(ROOMS[i].c),v=S.visited.includes(i);
    x.fillStyle=v?(S.lit[i]?'#d6a35a':'#3b4a6b'):'rgba(120,130,160,.35)';x.beginPath();x.arc(X,Y,v?14:9,0,7);x.fill();
    x.fillStyle=v?'#ece5d6':'rgba(236,229,214,.4)';x.fillText(v?ROOMS[i].name:'?',X,Y-24);}
  const [PX,PY]=pr(pos());x.fillStyle='#ff5a3a';x.beginPath();x.arc(PX,PY,10,0,7);x.fill();
  x.fillStyle='rgba(236,229,214,.6)';x.font='22px IBM Plex Sans, sans-serif';x.fillText('Планшет: модель Кэли — Клейна, косая проекция',W/2,W-60);}

// ───────── экраны ─────────
function screenShow(html){const e=screen;e.innerHTML=`<div class="card framed">${html}</div>`;e.classList.add('on');
  try{if(document.pointerLockElement)document.exitPointerLock();}catch(_){}
  e.querySelectorAll('[data-a]').forEach(b=>b.addEventListener('click',()=>act(b.dataset.a)));
  const m=e.querySelector('.btn.main');if(m)m.focus({preventScroll:true});e.querySelector('.card').scrollTop=0;}
function screenHide(){screen.classList.remove('on');screen.innerHTML='';}
function lock(){if(matchMedia('(pointer:coarse)').matches)return;try{const r=canvas.requestPointerLock();if(r&&r.catch)r.catch(()=>{});}catch(_){}}
function act(a){AU.init();
  if(a==='start'||a==='restart'){S=fresh();begin();say('Николай','Напрасное старание со времён Евклида, в продолжение двух тысяч лет, заставило меня подозревать, что в самих понятиях ещё не заключается той истины, которую хотели доказывать.',8);
    say('Николай','Линза — в Хранилище чертежей: из Атриума по Галерее и дальше через Переход. Лист 281 — в Зале переписи, за Картотекой.',8);}
  else if(a==='continue'){if(!S){S=fresh();}S.paused=false;screenHide();lock();}
  else if(a==='load'){if(load()){begin();}}
  else if(a==='quit'){exit();}
  else if(a==='save'){save();}
  else if(a==='sound'){AU.on=!AU.on;pause();}}
function begin(){S.paused=false;S.over=false;S.room=-1;screenHide();ui.obj();$('mplaque').style.display='none';$('msub').style.opacity=0;lock();}
function pause(){if(!S||S.over)return;S.paused=true;aiming=false;
  const lem=ITEMS.filter(i=>i.kind===2&&S.got[i.id]);
  screenShow(`<div class="ch">Пауза</div><h2>Архив лишних точек</h2>
  <div class="row"><button class="btn main" data-a="continue">Продолжить</button><button class="btn" data-a="save">Сохранить <span class="mono">(K)</span></button>
  ${hasSave()?'<button class="btn" data-a="load">Загрузить <span class="mono">(L)</span></button>':''}<button class="btn" data-a="restart">Заново</button><button class="btn" data-a="sound">Звук: ${AU.on?'вкл':'выкл'}</button><button class="btn" data-a="quit">Выйти в прогулку</button></div>
  <details ${lem.length?'open':''}><summary>Леммы: ${lem.length} / ${LEMMAS.length}</summary>${lem.map(i=>`<p><b>${LEMMAS[i.lemma].t}.</b> ${LEMMAS[i.lemma].x}</p>`).join('')||'<p>Пока ни одной. Леммы — золотые точки в тёмных комнатах.</p>'}</details>
  ${controlsHTML()}`);}
function controlsHTML(){return `<div class="ctrls"><b>W A S D</b><span>идти (пространство без «низа»: Пробел и C — вверх и вниз)</span><b>Shift</b><span>бежать — громко, стражи слышат</span>
  <b>ПКМ (держать)</b><span>геодезический рывок: прицел, отпустить — переместиться (тратит дефект)</span><b>V</b><span>Линза Абсолюта: стражи и их конусы взгляда сквозь стены</span>
  <b>F</b><span>усыпить стража со спины, взять предмет, погасить лампу</span><b>Tab</b><span>планшет-карта</span><b>K / L</b><span>сохранить / загрузить</span><b>Esc</b><span>пауза</span></div>`;}
function open(){if(!MP){alert('Шейдер миссии не собрался: '+(MPerr&&MPerr.message));return;}
  active=true;document.body.classList.add('mission');hudEl.classList.add('on');
  for(const id of ['top','panel','stats','hint','mapwrap'])$(id).style.visibility='hidden';
  if(!S)S=fresh();
  screenShow(`<div class="crest">${emblemSVG()}<div class="wordmark">Пятый Постулат</div><div class="ch">Глава 1</div><h2>Архив лишних точек</h2></div>
  <p>В переписи Города появилась лишняя точка — 281-й житель, которого нет ни в одном доме. Вера, чертёжница Церкви, ночью пробирается в Архив. Он сложен из додекаэдров с прямыми углами, а между залами патрулируют Чертёжники.</p>
  <p>Найдите <b>Линзу Абсолюта</b> и <b>лист 281</b> и уйдите через Окно на Абсолют. Стражей можно не трогать — а можно усыпить со спины.</p>
  <div class="q">Стелс здесь честный: видимый размер падает как 1/sh d. Издалека, во тьме и неподвижно вас почти не разглядеть.</div>
  ${controlsHTML()}
  <div class="row"><button class="btn main" data-a="start">Начать</button>${hasSave()?'<button class="btn" data-a="load">Продолжить с сохранения</button>':''}<button class="btn" data-a="quit">Назад к прогулке</button></div>`);
  S.paused=true;}
function exit(){active=false;aiming=false;mapOn=false;mapC.classList.remove('on');screenHide();hudEl.classList.remove('on');document.body.classList.remove('mission');
  for(const id of ['top','panel','stats','hint','mapwrap'])$(id).style.visibility='';
  document.getElementById('danger').style.opacity=0;AU.setDrone(0,false);
  if(S&&!S.over)S.paused=true;setWorld(world);
  try{if(document.pointerLockElement)document.exitPointerLock();}catch(_){}}

// ───────── ввод ─────────
function key(e,down){if(!active)return false;const k=e.code;
  if(screen.classList.contains('on'))return /^(Digit\d|KeyR|KeyH)$/.test(k);
  if(!down){if(k==='Tab'){mapOn=false;mapC.classList.remove('on');}if(k==='KeyB'&&aiming){aiming=false;doBlink();}return false;}
  if(k==='Tab'){e.preventDefault();mapOn=true;mapC.classList.add('on');return true;}
  if(k==='KeyF'){interact();return true;}
  if(k==='KeyV'){if(S.hasLens){S.lensOn=!S.lensOn&&S.mana>0.02;}else toast('Линзы ещё нет');return true;}
  if(k==='KeyB'){if(!e.repeat)aiming=true;return true;}
  if(k==='KeyK'){save();return true;}
  if(k==='KeyL'){if(hasSave()){load();begin();}return true;}
  if(k==='Escape'||k==='KeyP'){pause();return true;}
  if(/^(Digit\d|KeyR|KeyH)$/.test(k))return true;
  return false;}
canvas.addEventListener('contextmenu',e=>{if(active)e.preventDefault();});
canvas.addEventListener('mousedown',e=>{if(active&&e.button===2&&!S.paused&&!S.over)aiming=true;});
addEventListener('mouseup',e=>{if(active&&e.button===2&&aiming){aiming=false;if(!S.paused&&!S.over)doBlink();}});
document.addEventListener('pointerlockchange',()=>{if(active&&!document.pointerLockElement&&S&&!S.paused&&!S.over)pause();});
const tb=$('mt-blink');tb.addEventListener('pointerdown',e=>{aiming=true;tb.setPointerCapture(e.pointerId);});
tb.addEventListener('pointerup',()=>{if(aiming){aiming=false;doBlink();}});tb.addEventListener('pointercancel',()=>aiming=false);
$('mt-lens').addEventListener('click',()=>{if(S.hasLens)S.lensOn=!S.lensOn&&S.mana>0.02;else toast('Линзы ещё нет');});
$('mt-act').addEventListener('click',interact);$('mpause').addEventListener('click',pause);

function frame(dt,now){
  if(S&&!S.paused&&!S.over)update(dt);else look=[0,0];
  if(S)render(now);
  if(S&&now-(frame.h||0)>60){frame.h=now;hud();}
}
// кнопка в списке миров
{const b=document.createElement('button');b.innerHTML='<kbd>7</kbd>Миссия: Архив';b.style.borderColor='var(--brass)';b.addEventListener('click',open);worldsEl.appendChild(b);}
addEventListener('keydown',e=>{if(!active&&e.code==='Digit7'&&!(e.target.tagName==='INPUT'))open();});
if(location.hash==='#archive')setTimeout(open,0);

return {get active(){return active;},frame,key,open,exit,
  // для отладки и тестов
  _:{frameAt,faceCenter,RI,g,FOV,los,Guard,ROOMS,ITEMS,sdfWorld,roomOfPoint,get S(){return S;},set S(v){S=v;},fresh,pos,update,serialize,deserialize,blinkTarget}};
})();
window.MISSION=MISSION;
