'use strict';
// ═══════════════ «Пятый Постулат»: кампания ═══════════════
// Пролог и пять глав в четырёх геометриях:
//   flat  — евклидов город (пролог);
//   rooms — соты из многогранников: {5,3,4} (Архив, Тюрьма) и {4,3,5} (Цитадель);
//   house — башня на орисферах (верхнее полупространство, этажи высотой ln 2);
//   plane — равнина {5,4} (эквидистанта над плоскостью Лобачевского).
// Стражи, предметы и персонажи живут в абсолютных координатах R^{3,1} (в прологе — в R^3)
// и рисуются как SDF-фигуры внутри ограничивающих шаров; пересечение луча с шаром — в замкнутой форме.
const GAME=(()=>{
// ───────── алгебра ─────────
function linv(G){const R=new Array(16),J=[1,1,1,-1];for(let c=0;c<4;c++)for(let r=0;r<4;r++)R[c*4+r]=J[r]*G[r*4+c]*J[c];return R;}
function det4(m){const a=(r,c)=>m[c*4+r];let s=0;
  for(let c=0;c<4;c++){const k=[0,1,2,3].filter(x=>x!==c);
    s+=(c%2?-1:1)*a(0,c)*det3(a(1,k[0]),a(1,k[1]),a(1,k[2]),a(2,k[0]),a(2,k[1]),a(2,k[2]),a(3,k[0]),a(3,k[1]),a(3,k[2]));}
  return s;}
function perpAt(p,u,hint){for(const b of [hint||[0,1,0,0],[0,1,0,0],[1,0,0,0],[0,0,1,0]]){let w=b.map((x,i)=>x+md(b,p)*p[i]);const e=md(w,u);w=w.map((x,i)=>x-e*u[i]);
  if(md(w,w)>1e-4)return tangent(w,p);}return tangent([0,1,0,0],p);}
function frameAt(p,fwd,upHint){p=normalizePoint(p);const f=tangent(fwd,p),up=perpAt(p,f,upHint);
  let r=[1,0,0,0];for(const b of [[1,0,0,0],[0,0,1,0],[0,1,0,0]]){let w=b.map((x,i)=>x+md(b,p)*p[i]);
    for(const e of [f,up]){const d=md(w,e);w=w.map((x,i)=>x-d*e[i]);}if(md(w,w)>1e-4){r=tangent(w,p);break;}}
  const M=[...r,...up,...f,...p];if(det4(M)<0)for(let i=0;i<4;i++)M[i]=-M[i];return M;}
const far=d=>{const l=Math.hypot(...d),s=Math.sinh(9);return [s*d[0]/l,s*d[1]/l,s*d[2]/l,Math.cosh(9)];};
const mid=(a,b)=>normalizePoint(a.map((x,i)=>x+b[i]));
const fromHS=q=>{const w=1/q[2],u=(q[0]*q[0]+q[1]*q[1]+q[2]*q[2])/q[2];return [q[0]*w,q[1]*w,(u-w)/2,(u+w)/2];};
const toHS=p=>{const z=1/(p[3]-p[2]);return [p[0]*z,p[1]*z,z];};
const polar=(r,deg)=>{const a=deg*Math.PI/180;return [Math.sinh(r)*Math.cos(a),Math.sinh(r)*Math.sin(a),0,Math.cosh(r)];};
const atHeight=(f,h)=>{const ch=Math.cosh(h),sh=Math.sinh(h);return [f[0]*ch,f[1]*ch,sh,f[3]*ch];};
const footOf=p=>{const h=Math.asinh(p[2]),c=Math.cosh(h);return normalizePoint([p[0]/c,p[1]/c,0,p[3]/c]);};

// ───────── общий GLSL: фигуры и материалы ─────────
const OBJ_SDF=`
uniform float uTime;
float gPar;
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
// Фигура: стилизованный человек (пропорции Dishonored — крупные кисти и голова, длинное пальто).
// vr: 0 чертёжник, 1 Кассель, 2 Орицикла, 3 Бернхард, 4 отражение Веры, 5 Евклид, 6 тюремщик,
//     7 надзиратель с фонарём, 8 циркулятор, 9 страж Цитадели, 10 ребёнок. gWalk: 0 стоит, 1 идёт, 2 бежит.
float gWalk=0.;
float sdLimb(vec3 p,vec3 a,vec3 b,float ra,float rb){ vec3 pa=p-a, ba=b-a; float h=clamp(dot(pa,ba)/dot(ba,ba),0.,1.); return length(pa-ba*h)-mix(ra,rb,h); }
vec3 swingX(vec3 v,float a){ float c=cos(a), s=sin(a); return vec3(v.x, c*v.y-s*v.z, s*v.y+c*v.z); }
void put(inout float d,inout int m,float dd,int mm){ if(dd<d){d=dd;m=mm;} }
float figureSDF(vec3 q,float sl,int vr,out int m){
  float scl=vr==10?1.7:1.; q*=scl; q.y-=0.012;
  float wk=sl>.5?0.:gWalk, ph=uTime*(wk>1.5?10.5:6.2)+float(vr)*1.7, sw=wk>0.? sin(ph):0., amp=wk>1.5?0.75:0.45;
  if(sl>.5){ q.xy=rot(1.25)*q.xy; q.y+=0.05; q.x+=0.03; }
  else{
    q.y+=0.004*sin(uTime*1.7+float(vr))-0.004*abs(sw)*wk;      // дыхание и шаг
    q.xy=rot(0.035*sin(uTime*1.3+float(vr)*1.3)+0.04*sw*wk*0.5)*q.xy;
    q.yz=rot(-0.22*clamp(gPar,0.,1.)-0.12*step(1.5,wk))*q.yz;    // подаётся вперёд: насторожен или бежит
  }
  bool robe= vr==2||vr==5||vr==10;                             // длинное одеяние до пола
  bool bare= vr==2||vr==3||vr==4||vr==5||vr==10;               // открытое лицо
  m=1; float d=1e9;
  // ноги и сапоги
  for(int i=0;i<2;i++){ float sd=i==0?1.:-1.; float a=sd*sw*amp, a2=a-0.55*amp*max(0.,-sd*cos(ph))*step(.5,wk);
    vec3 H=vec3(sd*0.016,-0.022,0.), K=H+swingX(vec3(0,-0.056,0),-a), A=K+swingX(vec3(0,-0.052,0),-a2);
    put(d,m,sdLimb(q,H,K,0.0125,0.0095),21); put(d,m,sdLimb(q,K,A,0.0098,0.0082),20);
    vec3 fq=q-A-vec3(0,-0.006,0.006); fq=swingX(fq,a2*0.6); put(d,m,sdEll(fq,vec3(0.0085,0.0065,0.0165)),20); }
  // торс: грудь, живот, ремень
  float tor=smin(sdEll(q-vec3(0,0.034,0.002),vec3(0.041,0.034,0.027)),sdEll(q-vec3(0,0.0,0),vec3(0.032,0.03,0.024)),0.012);
  put(d,m,tor,1);
  put(d,m,sdTorZ((q-vec3(0,-0.004,0)).xzy,0.031,0.004),20);
  put(d,m,sdBox(q-vec3(0,-0.004,0.033),vec3(0.006,0.005,0.002)),2);
  if(!robe){ float by=q.y-0.012; by-=0.014*clamp(floor(by/0.014+0.5),0.,2.);                     // двубортный ряд пуговиц
    put(d,m,length(vec3(abs(q.x)-0.011,by,q.z-0.0265+max(0.,0.012-q.y)*0.25))-0.0026,2); }
  // пальто: расширяется книзу, спереди разрез; у мантий — до пола
  { float y0=0.002, y1=robe?-0.138:-0.108; float t=clamp((y0-q.y)/(y0-y1),0.,1.);
    float rr=mix(0.034,robe?0.058:0.052,t)+0.005*abs(sw)*t*wk, ang=atan(q.x,q.z);
    rr+=0.0024*sin(ang*6.+q.y*55.)*t;                                     // складки
    float coat=max(length(vec2(q.x,q.z*1.18))-rr, max(q.y-y0, y1-q.y));
    if(!robe) coat=max(coat,-(max(abs(q.x)-0.0015-0.016*t*t, 0.012-q.z)));  // разрез спереди
    coat=max(coat,-max(length(vec2(q.x,q.z*1.18))-rr+0.004, y1+0.004-q.y)); // полое внутри (видны ноги)
    put(d,m,coat*0.8,1); }
  // плечевая пелерина и наплечники
  put(d,m,smin(sdEll(q-vec3(0,0.054,-0.003),vec3(0.054,0.016,0.034)),sdEll(q-vec3(0,0.04,-0.006),vec3(0.05,0.026,0.031)),0.01),1);
  float pa=sdEll(vec3(abs(q.x),q.y,q.z)-vec3(0.047,0.062,0.0),vec3(0.017,0.01,0.019)); put(d,m,pa,2);
  // руки: плечо → локоть → запястье, крупные кисти; размах против ног
  for(int i=0;i<2;i++){ float sd=i==0?1.:-1.; float b=-sd*sw*amp*0.75;
    vec3 Sh=vec3(sd*0.047,0.056,0.), E=Sh+swingX(vec3(sd*0.008,-0.042,0.),-b), W=E+swingX(vec3(-sd*0.002,-0.04,0.),-b-0.25-0.35*step(1.5,wk));
    if(vr==1&&i==1){ E=Sh+vec3(-0.008,-0.03,0.022); W=E+vec3(0.0,-0.004,0.034); }        // Кассель держит маятник перед собой
    if(vr==7&&i==0){ E=Sh+vec3(0.01,-0.035,0.015); W=E+vec3(0.0,0.01,0.03); }           // надзиратель держит фонарь
    put(d,m,sdLimb(q,Sh,E,0.0112,0.0092),1); put(d,m,sdLimb(q,E,W,0.0092,0.0078),1);
    put(d,m,sdTorZ((q-W-vec3(0,0.006,0)).xzy,0.0085,0.0028),bare?1:20);                  // манжета
    put(d,m,sdEll(q-W-vec3(0,-0.009,0.002),vec3(0.0062,0.0105,0.0082)),bare?19:20);
    put(d,m,sdCaps(q,W+vec3(-sd*0.004,-0.002,0.006),W+vec3(-sd*0.006,-0.009,0.009),0.0026),bare?19:20); }   // большой палец   // кисть (перчатка)
  // шея, стоячий воротник
  put(d,m,sdCaps(q,vec3(0,0.06,0),vec3(0,0.08,0.002),0.0085),bare?19:21);
  { float col=max(abs(length(vec2(q.x,q.z+0.002))-0.019+(q.y-0.064)*0.15)-0.0022, abs(q.y-0.072)-0.012); col=max(col,q.z-0.012-(q.y-0.06)*0.6); put(d,m,col,1); }
  // голова: череп, удлинённая челюсть, нос, брови
  vec3 hq=q-vec3(0,0.094,0.001);
  float head=smin(sdSph(hq,0.0185),sdEll(hq-vec3(0,-0.011,0.006),vec3(0.0135,0.0155,0.0145)),0.008);
  put(d,m,head,19);
  if(bare){ put(d,m,sdCaps(hq,vec3(0,0.001,0.017),vec3(0,-0.006,0.023),0.0032),19);
    put(d,m,sdCaps(hq,vec3(-0.009,0.0045,0.0145),vec3(0.009,0.0045,0.0145),0.0022),19);
    float eye=min(sdSph(hq-vec3(0.0065,0.0005,0.0158),0.0026),sdSph(hq-vec3(-0.0065,0.0005,0.0158),0.0026)); put(d,m,eye,23); }
  else{ // маска Чертёжников: фарфоровая, с латунным моноклем-линзой
    put(d,m,sdEll(hq-vec3(0,-0.004,0.010),vec3(0.0165,0.021,0.0125)),3);
    put(d,m,sdTorZ((hq-vec3(0,-0.004,0.006))*vec3(1.,0.8,1.),0.0155,0.0016),2);                // латунный обод маски
    put(d,m,sdEll(hq-vec3(0,-0.016,0.019),vec3(0.008,0.0055,0.006)),2);                              // дыхало
    vec3 e=hq-vec3(0.0065,0.002,0.0215);
    put(d,m,sdTorZ(e,0.0068,0.0022),2); put(d,m,sdEll(e,vec3(0.006,0.006,0.0028)),4);
    put(d,m,sdEll(hq-vec3(-0.0065,0.002,0.0205),vec3(0.004,0.0022,0.002)),23); }
  // капюшоны, шляпы, причёски
  if(vr==0||vr==1||vr==2||vr==9){ float hood=max(sdSph(hq-vec3(0,0.003,-0.004),0.025),-(hq.z-0.013));
    hood=max(hood,-sdSph(hq-vec3(0,0.001,0.003),0.0215)); hood=smin(hood,sdEll(q-vec3(0,0.066,-0.012),vec3(0.03,0.016,0.022)),0.01); put(d,m,hood,5); }
  if(vr==4) put(d,m,smin(sdSph(hq-vec3(0,0.006,-0.004),0.0195),sdSph(hq-vec3(0,0.008,-0.022),0.009),0.006),22);  // Вера: волосы в узел
  if(vr==10) put(d,m,sdSph(hq-vec3(0,0.006,-0.004),0.0198),22);
  if(vr==3){ put(d,m,sdEll(hq-vec3(0,-0.017,0.011),vec3(0.0135,0.016,0.0095)),22);                               // борода Бернхарда
    put(d,m,sdEll(hq-vec3(0,0.012,-0.002),vec3(0.021,0.007,0.021)),5); }                                            // плоская шапка
  if(vr==5) put(d,m,sdRCone(hq-vec3(0,0.012,-0.002),0.02,0.008,0.038),5);                                          // митра
  if(vr==7) put(d,m,max(sdRCone(hq-vec3(0,-0.002,-0.006),0.026,0.002,0.06),-sdSph(hq-vec3(0,0.0,0.004),0.021)),5); // остроконечный капюшон
  if(vr==8){ put(d,m,sdEll(hq-vec3(0,0.012,0),vec3(0.046,0.0028,0.046)),5); put(d,m,sdEll(hq-vec3(0,0.02,0),vec3(0.0175,0.011,0.0175)),5); }
  if(vr==6){ put(d,m,max(sdSph(hq-vec3(0,0.002,-0.002),0.0235),-(hq.y+0.002)),2); put(d,m,sdTorZ((hq-vec3(0,-0.002,-0.002)).xzy,0.024,0.003),2);
    put(d,m,sdTorZ((q-vec3(-0.034,-0.016,0.016)).zyx,0.011,0.0022),2); }                                            // шлем и связка ключей
  if(vr==9) put(d,m,sdTorZ(hq-vec3(0,0.004,-0.03),0.03,0.0024),2);                                               // нимб-обод
  // атрибуты: циркуль на бедре, маятник, фонарь
  if(vr==0||vr==8){ float c1=sdCaps(q,vec3(0.036,0.0,0.012),vec3(0.046,-0.07,0.022),0.0026), c2=sdCaps(q,vec3(0.036,0.0,0.012),vec3(0.028,-0.07,0.03),0.0026);
    put(d,m,min(min(c1,c2),sdSph(q-vec3(0.036,0.002,0.012),0.0055)),2); }
  if(vr==1){ vec3 pq=q-vec3(-0.008,0.024,0.058); pq.xy=rot(0.6*sin(uTime*2.4))*pq.xy;
    put(d,m,min(sdCaps(pq,vec3(0),vec3(0,-0.07,0),0.0013),sdOct(pq-vec3(0,-0.078,0),0.013)),2); }
  if(vr==7){ vec3 lq=q-vec3(0.05,0.04,0.045); put(d,m,sdCaps(lq,vec3(0,-0.005,0),vec3(0,0.012,0),0.0016),2); put(d,m,sdEll(lq-vec3(0,-0.018,0),vec3(0.011,0.014,0.011)),15); }
  return d/scl;
}
float objSDF(int kind,vec3 q,float sl,int vr,out int m){
  if(kind==1||kind==8||kind==10) return figureSDF(q,sl,vr,m);
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
  if(kind==9){ // Главная Машина Прямизны: гироскоп из трёх ортогональных колец
    vec3 a=q; a.xy=rot(uTime*0.5)*a.xy; vec3 b=q.yzx; b.xy=rot(uTime*0.7)*b.xy; vec3 c=q.zxy; c.xy=rot(-uTime*0.9)*c.xy;
    float d=min(min(sdTorZ(a,0.22,0.012),sdTorZ(b,0.18,0.012)),sdTorZ(c,0.14,0.012)); m=2;
    float core=sdSph(q,0.055); if(core<d){d=core;m=12;} return d; }
  if(kind==12){ float bob=sdRCone(q-vec3(0,-0.055,0),0.002,0.018,0.035); float st=sdCaps(q,vec3(0,-0.02,0),vec3(0,0.07,0),0.0012);
    float hk=sdTorZ(q-vec3(0,0.072,0),0.006,0.0015); m=2; return min(min(bob,st),hk); }
  if(kind==13){ float arc=max(sdTorZ(q,0.045,0.004),-q.y); float bar=sdCaps(q,vec3(-0.047,0,0),vec3(0.047,0,0),0.003);
    vec3 n=q; n.xy=rot(sin(uTime*2.3)*1.2)*n.xy; float nd=sdCaps(n,vec3(0),vec3(0,0.04,0),0.0018);
    float d=min(arc,bar); m=2; if(nd<d){d=nd;m=13;} return d; }
  if(kind==15){ float ob=max(sdBox(q,vec3(0.026,0.09,0.026)),dot(vec3(abs(q.x),q.y,abs(q.z)),normalize(vec3(1,0.55,1)))-0.072);
    float band=sdBox(q-vec3(0,0.03,0),vec3(0.0275,0.008,0.0275)); m=14; if(band<ob+0.001){m=13;} return min(ob,band); }
  if(kind==16){ float rr=length(q.xy); float ring=sdTorZ(q,0.40,0.012);
    float bx=abs(mod(q.x+0.065,0.13)-0.065), by=abs(mod(q.y+0.065,0.13)-0.065);
    float bars=max(min(length(vec2(bx,q.z)),length(vec2(by,q.z)))-0.012,rr-0.40);
    m=2; return min(ring,bars); }
  if(kind==20){ float base=sdBox(q-vec3(0,-0.03,0),vec3(0.05,0.035,0.045));
    float roof=max(sdBox(q-vec3(0,0.03,0),vec3(0.06,0.035,0.055)),dot(vec3(abs(q.x),q.y,0.),normalize(vec3(1.,1.3,0.)))-0.045);
    float win=sdBox(q-vec3(0,-0.03,0.046),vec3(0.012,0.014,0.002));
    float d=min(base,roof); m=base<roof?14:16; if(win<d+0.001){d=min(d,win);m=15;} return d; }
  if(kind==21){ vec3 r=q; r.xy=rot(uTime*2.)*r.xy; float core=sdSph(q,0.014), ring=sdTorZ(r,0.035,0.003), ring2=sdTorZ(r.yzx,0.028,0.0025);
    m=13; return min(core,min(ring,ring2)); }
  if(kind==19){ vec3 r=q-vec3(0,0.02,0); r.yz=rot(0.55)*r.yz; float tube=sdCaps(r,vec3(0,-0.04,0),vec3(0,0.06,0),0.011);
    float rings=min(sdTorZ(r.xzy-vec3(0,0,0.03),0.013,0.003),sdTorZ(r.xzy-vec3(0,0,-0.02),0.013,0.003));
    float lens=sdSph(r-vec3(0,0.062,0),0.009), stand=sdCaps(q,vec3(0,0.0,0),vec3(0,-0.09,0),0.004);
    float d=min(min(tube,rings),stand); m=2; if(lens<d){d=lens;m=6;} return d; }
  if(kind==18){ q.xz=rot(uTime*0.7)*q.xz; float l1=sdCaps(q,vec3(0,0.04,0),vec3(-0.022,-0.05,0),0.004), l2=sdCaps(q,vec3(0,0.04,0),vec3(0.022,-0.05,0.004),0.004);
    float hg=sdSph(q-vec3(0,0.046,0),0.009), arc=max(sdTorZ(q-vec3(0,0.04,0),0.05,0.0025),q.y-0.0); m=2; return min(min(l1,l2),min(hg,arc)); }
  if(kind==17){ // чертёжный стол: наклонная доска с синькой, лампа на латунной стойке
    vec3 b=q-vec3(0,0.03,0); b.yz=rot(-0.45)*b.yz;
    float board=sdBox(b,vec3(0.065,0.003,0.045)), top=sdBox(q-vec3(0,0.012,0),vec3(0.07,0.004,0.05));
    vec3 lq=vec3(abs(q.x),q.y,abs(q.z));float legs=sdCaps(lq,vec3(0.06,0.012,0.04),vec3(0.06,-0.085,0.04),0.004);
    float arm=sdCaps(q,vec3(0.06,0.02,-0.04),vec3(0.05,0.1,-0.03),0.0025), lmp=sdSph(q-vec3(0.05,0.1,-0.03),0.012);
    float paper=sdBox(b-vec3(0,0.0036,0),vec3(0.05,0.0008,0.035));
    float d=min(board,top); m=16; if(legs<d){d=legs;m=16;} if(arm<d){d=arm;m=2;} if(lmp<d){d=lmp;m=15;} if(paper<d){d=paper;m=18;} return d; }
  m=0; return sdSph(q,0.03);
}
// материалы объектов: m — номер материала фигуры, vr — вариант персонажа
void objMat(int mm,int kind,int vr,float par,float sl,vec3 q,float f,vec4 X,out vec3 base,out float metal,out float rough,out vec3 emis){
  base=vec3(0.5); metal=0.; rough=0.6; emis=vec3(0.);
  vec3 robe= vr==1? vec3(0.30,0.035,0.04) : vr==2? vec3(0.05,0.13,0.09) : vr==3? vec3(0.20,0.12,0.07) : vr==5? vec3(0.80,0.78,0.72)
: vr==10? vec3(0.55,0.33,0.28) : vr==6? vec3(0.17,0.17,0.19) : vr==7? vec3(0.09,0.08,0.16) : vr==8? vec3(0.24,0.18,0.09) : vr==9? vec3(0.86,0.84,0.79) : vec3(0.07,0.08,0.13);
  if(mm==1){ base=robe*(0.78+0.4*fbm(vec3(q.x*110.,q.y*26.,q.z*110.))); rough=0.82;
    if(q.y<-0.004&&q.z>0.0&&abs(q.x)<0.022&&f<0.35) base=mix(base,vec3(0.32,0.05,0.06),0.6);             // подкладка в разрезе
    if(q.y>0.07&&q.y<0.088&&abs(abs(q.y-0.079)-0.008)<0.0016) base=mix(base,vec3(0.85,0.7,0.4),0.7);     // кант воротника
    if(abs(q.y-(vr==2||vr==5||vr==10?-0.133:-0.103))<0.004||(vr!=2&&vr!=5&&vr!=10&&abs(q.x)<0.007&&q.z>0.015&&q.y<0.0&&q.y>-0.1)){ brass(X,base,rough); metal=1.; } }
  else if(mm==5){ base=robe*0.65; rough=0.85; if(vr==5){ brass(X,base,rough); metal=1.; } }
  else if(mm==2){ brass(X,base,rough); metal=1.; if(vr==1){ base*=vec3(1.05,0.85,0.75); }
    if(kind==1&&q.y>0.085&&q.y<0.096&&abs(q.x)<0.008&&q.z>0.02&&fract(q.x*420.)<0.45) base*=0.25; }
  else if(mm==3){ base=vec3(0.86,0.83,0.77)*(0.9+0.15*fbm(q*300.)); rough=0.32; if(vr==3) base=vec3(0.62,0.45,0.34);
    if(vr==6){ base=vec3(0.30,0.30,0.32); metal=1.; rough=0.45; } if(vr==9){ brass(X,base,rough); metal=1.; } }
  else if(mm==15){ base=vec3(0.1); emis=vec3(1.0,0.78,0.45)*(3.0+0.6*sin(uTime*9.)); }
  else if(mm==4){ base=vec3(0.02); rough=0.1; emis= sl>.5? vec3(0.) : mix(vec3(1.,0.72,0.28),vec3(1.,0.12,0.05),par)*(3.5+1.5*sin(uTime*6.)*par); }
  else if(mm==6){ base=vec3(0.05,0.08,0.12); rough=0.05; emis=vec3(0.25,0.55,1.0)*(0.5+2.2*pow(1.-f,3.)); }
  else if(mm==7){ base=vec3(0.45,0.05,0.04); rough=0.35; }
  else if(mm==8){ base=vec3(0.86,0.80,0.66); rough=0.9;
    if(abs(q.x)<0.024&&q.y>-0.02&&q.y<0.036&&fract(q.y*110.)<0.3) base=vec3(0.22,0.18,0.14); emis=base*0.06; }
  else if(mm==9){ base=vec3(0.2); emis=vec3(1.0,0.75,0.32)*(2.5+1.2*sin(uTime*3.)); }
  else if(mm==10){ base=vec3(0.30,0.15,0.55); rough=0.12; emis=vec3(0.55,0.25,1.0)*(0.5+0.8*pow(1.-f,2.))*(1.+0.4*sin(uTime*4.)); }
  else if(mm==11){ float sw=fbm(vec3(q.xy*28.+vec2(sin(uTime*0.3),cos(uTime*0.27)),uTime*0.25));
    emis=mix(vec3(0.30,0.55,1.0),vec3(0.95,0.97,1.0),smoothstep(0.35,0.75,sw))*(0.55+0.85*par)*(0.55+0.45*smoothstep(0.122,0.03,length(q.xy))); base=vec3(0.02); }
  else if(mm==12){ base=vec3(1.); emis=vec3(1.0,0.92,0.75)*(2.2+0.8*sin(uTime*8.)); }
  else if(mm==13){ base=vec3(0.1); emis=(kind==13? vec3(0.7,0.35,1.0) : kind==21? vec3(0.55,1.0,0.7)*1.6 : vec3(0.35,0.8,1.0))*(1.6+0.8*sin(uTime*3.))*(1.-0.85*par); }
  else if(mm==16){ base=vec3(0.22,0.12,0.06)*(0.75+0.5*fbm(q*160.)); rough=0.5; }
  else if(mm==18){ base=vec3(0.10,0.22,0.42); rough=0.9; float gl=max(step(fract(q.x*90.),0.08),step(fract(q.z*90.),0.08)); emis=vec3(0.45,0.7,1.0)*(0.12+0.25*gl)*(1.+2.*par); }
  else if(mm==19){ base=vr==3? vec3(0.62,0.44,0.34) : vr==10? vec3(0.86,0.66,0.55) : vr==5? vec3(0.78,0.66,0.58) : vec3(0.80,0.60,0.50); rough=0.55; base*=0.92+0.12*fbm(q*420.); }
  else if(mm==20){ base=vec3(0.13,0.075,0.045)*(0.8+0.4*fbm(q*260.)); rough=0.42; }
  else if(mm==21){ base=robe*0.45+vec3(0.03); rough=0.85; }
  else if(mm==22){ base=vr==3? vec3(0.62,0.6,0.56) : vr==4? vec3(0.16,0.09,0.05) : vec3(0.25,0.15,0.08); rough=0.7; base*=0.8+0.4*fbm(vec3(q.x*500.,q.y*120.,q.z*500.)); }
  else if(mm==23){ base=vec3(0.02); rough=0.2; emis=vr==1? vec3(1.,0.15,0.05)*(0.6+2.*par) : vec3(0.); }
  else if(mm==14){ base=vec3(0.55,0.53,0.50)*(0.8+0.3*fbm(q*120.)); rough=0.8; }
  if(kind==10){ emis+=vec3(0.35,0.75,1.0)*(0.6+0.6*pow(1.-f,2.)); base*=0.3; }
}`;
// трассировка и освещение объектов в гиперболических мирах
const OBJ_H=`
#define NO 16
uniform vec4 uO[NO]; uniform vec4 uOR[NO]; uniform vec4 uOU[NO]; uniform vec4 uOD[NO]; uniform vec4 uOK[NO]; uniform vec4 uOC[NO]; uniform int uNO;
uniform vec4 uMark; uniform float uMarkOn; uniform float uLens; uniform float uCosFov; uniform float uView;
float gTO, gTG, gTI; int gIO;
int okind(int j){ return int(uOK[j].x+.5); }
float osl(int j){ return mod(uOK[j].w,2.); }
float olit(int j){ return mod(floor(uOK[j].w*0.5+0.01),2.); }
int ovar(int j){ return int(mod(floor(uOK[j].w*0.25+0.01),32.)); }
float owalk(int j){ return floor(uOK[j].w/128.+0.001); }
void traceObjects(vec4 p0, vec4 v0){
  gTO=1e9; gTG=1e9; gTI=1e9; gIO=-1;
  for(int j=0;j<NO;j++){ if(j>=uNO) break;
    vec4 C=uO[j]; float R=uOK[j].y; float A=-md(p0,C), B=-md(v0,C), k=cosh(R);
    float disc=k*k-A*A+B*B; if(disc<=0.) continue;
    float sq=sqrt(disc), u1=(k-sq)/(A+B), u2=(k+sq)/(A+B);
    if(u2<=1.) continue;
    float t0=u1>1.? log(u1) : 0., t1=log(u2);
    int kind=okind(j); float sl=osl(j); int vr=ovar(j); gPar=uOK[j].z; gWalk=owalk(j);
    if(kind==1){ if(sl<.5) gTG=min(gTG,t0); } else if(kind!=16&&kind!=10) gTI=min(gTI,t0);
    if(t0>=gTO) continue;
    float tt=t0;
    for(int s=0;s<56;s++){
      vec4 X=cosh(tt)*p0+sinh(tt)*v0; vec3 q=vec3(md(X,uOR[j]),md(X,uOU[j]),md(X,uOD[j]));
      int m; float dd=objSDF(kind,q,sl,vr,m);
      if(dd<2.5e-4){ if(tt<gTO){gTO=tt;gIO=j;} break; }
      tt+=dd; if(tt>t1) break;
    }
  }
}
vec3 shadeObject(vec4 p0, vec4 v0, vec3 lampC){
  int j=gIO; int kind=okind(j); float sl=osl(j), litO=olit(j), par=uOK[j].z; int vr=ovar(j); gPar=par; gWalk=owalk(j);
  float tO=gTO; vec4 X=cosh(tO)*p0+sinh(tO)*v0, vX=sinh(tO)*p0+cosh(tO)*v0;
  vec3 q=vec3(md(X,uOR[j]),md(X,uOU[j]),md(X,uOD[j]));
  int mm; const vec2 h=vec2(1.,-1.)*0.0006;
  vec3 nq=normalize(h.xyy*objSDF(kind,q+h.xyy,sl,vr,mm)+h.yyx*objSDF(kind,q+h.yyx,sl,vr,mm)+h.yxy*objSDF(kind,q+h.yxy,sl,vr,mm)+h.xxx*objSDF(kind,q+h.xxx,sl,vr,mm));
  objSDF(kind,q,sl,vr,mm);
  vec4 n=tp(nq.x*uOR[j]+nq.y*uOU[j]+nq.z*uOD[j],X);
  vec4 Lc=uOC[j]; vec4 L=tp(Lc,X); float sr=sinh(acosh(max(-md(X,Lc),1.))); float att=1.6/(0.18+sr*sr)*(0.25+0.75*litO);
  float f=clamp(-md(n,vX),0.,1.);
  vec3 base, emis; float metal, rough;
  objMat(mm,kind,vr,par,sl,q,f,X,base,metal,rough,emis);
  vec3 dirL=brdf(base,metal,rough,n,vX,L,X)*lampC*att;
  if(kind==1||kind==8||kind==10){
    // ступенчатая светотень с мягкими переходами (как LUT-рампа в cel shading) + цветной контур-свет
    float ndl=clamp(md(n,L),0.,1.); att=att/(1.+0.3*att); float ramp=0.16+0.44*smoothstep(0.03,0.14,ndl)+0.40*smoothstep(0.48,0.6,ndl);
    vec3 toon=base*ramp*lampC*att*0.42; dirL=brdf(base,metal,rough,n,vX,L,X)*lampC*att;
    dirL=mix(dirL,toon+dirL*0.25,0.7*(1.-metal));
    vec3 rimC=mix(vec3(0.42,0.62,1.0),vec3(1.0,0.38,0.14),clamp(par,0.,1.));
    float rim=smoothstep(0.55,0.95,1.-f)*(0.5+0.5*clamp(1.-ndl,0.,1.));
    return dirL+ambEnv(n,vX,L,lampC,att,base,metal,rough,1.)*1.25+emis+rimC*rim*0.32+base*0.02;
  }
  return dirL+ambEnv(n,vX,L,lampC,att,base,metal,rough,1.)+emis+vec3(0.25,0.35,0.6)*pow(1.-f,4.)*0.22;
}
float sphereT(vec4 p0, vec4 v0, vec4 C, float R){
  float A=-md(p0,C), B=-md(v0,C), k=cosh(R);
  if(A<=k) return 1e9; float disc=k*k-A*A+B*B; if(disc<=0.) return 1e9;
  float u=(k-sqrt(disc))/(A+B); if(u<=1.) return 1e9; return log(u);
}
vec3 overlays(vec3 col, inout float tHit, vec4 p0, vec4 v0){
  if(uLens>0.){
    col=mix(col,vec3(dot(col,vec3(.3,.5,.2)))*vec3(0.55,0.8,1.25),0.45*uLens);
    if(gTG<tHit-0.01) col=mix(col,vec3(1.,0.42,0.18),0.6*uLens);
    if(gTI<tHit-0.01) col=mix(col,vec3(1.,0.85,0.40),0.5*uLens);
    if(tHit<1e8){
      vec4 P=cosh(tHit)*p0+sinh(tHit)*v0;
      for(int j=0;j<NO;j++){ if(j>=uNO) break; if(okind(j)!=1||osl(j)>.5) continue;
        float dist=acosh(max(-md(P,uO[j]),1.)); if(dist>uView||dist<0.02) continue;
        if(md(tp(P,uO[j]),uOD[j])>uCosFov) col=mix(col,vec3(1.,0.18,0.08),0.28*uLens*(1.-dist/uView)); }
    }
  }
  if(uMarkOn>.5){ float tm=sphereT(p0,v0,uMark,0.06); if(tm<tHit){ col=mix(col,vec3(0.55,0.92,1.0)*2.2,0.6); tHit=tm; } }
  return col;
}`;

// ───────── шейдер комнат-многогранников ─────────
const NK=16;
const FS_RM=HEAD+`
#define NK ${NK}
uniform vec4 uM[4]; uniform vec4 uE1; uniform vec4 uE2; uniform vec4 uV; uniform float uBall; uniform float uCamPar;
uniform vec4 uF[3]; uniform vec4 uA[4];
uniform vec4 uK[NK]; uniform float uLit[NK]; uniform vec4 uRC[NK]; uniform int uNK;
uniform int uPal; uniform vec3 uLampC; uniform float uStraight;
const vec3 FOG=vec3(0.010,0.013,0.030);
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
}` + NORMAL + MAT + OBJ_SDF + OBJ_H + `
float wallH(vec4 p){ float e=edgeDist(p), r=acosh(max(-md(p,uP1),1.));
  float h=0.008*smoothstep(0.045,0.06,e)*(1.-smoothstep(0.105,0.118,e));
  h+=0.003*exp(-pow((e-0.075)/0.006,2.));
  h-=0.003*exp(-pow((e-0.13)/0.006,2.));
  h+=0.006*(1.-smoothstep(0.155,0.162,r));
  h-=0.002*(1.-smoothstep(0.125,0.13,r));
  if(uPal==1){ float a=asinh(abs(md(p,uM[2]))); h-=0.004*(1.-smoothstep(0.004,0.008,abs(mod(r,0.11)-0.055)))*step(0.17,r);
    h-=0.004*(1.-smoothstep(0.004,0.008,abs(mod(a,0.09)-0.045)))*step(0.17,r); h+=0.004*fbm(p.xyz*30.); }
  h+=0.0015*fbm(p.xyz*45.);
  return h; }
float surfH(vec4 p,int id){ if(id==1) return edgeH(p); if(id>=5) return wallH(p); return 0.; }
void wallMat(vec4 p,int room,out vec3 base,out float metal,out float rough){
  float e=edgeDist(p), r=acosh(max(-md(p,uP1),1.)), a=asinh(abs(md(p,uM[2]))), b=asinh(abs(md(p,uM[3])));
  int k=room<0?0:room-4*(room/4);
  float st=fbm(p.xyz*5.+float(room)*1.7);
  metal=0.; rough=0.85;
  if(uPal==1){ // тюрьма: тёсаный камень, железо
    base=vec3(0.20,0.21,0.23)*(0.6+0.7*st)*(0.85+0.3*fbm(p.xyz*24.));
    float mortar=max(1.-smoothstep(0.004,0.008,abs(mod(r,0.11)-0.055)),1.-smoothstep(0.004,0.008,abs(mod(a,0.09)-0.045)))*step(0.17,r);
    base=mix(base,vec3(0.07),mortar*0.8);
    base=mix(base,vec3(0.22,0.14,0.08),smoothstep(0.55,0.85,fbm(p.xyz*9.+2.))*0.5);
    if(e<0.118){ base=vec3(0.16,0.16,0.17); metal=1.; rough=0.55; if(abs(e-0.075)<0.0065) base=vec3(0.28,0.27,0.26); }
    if(r<0.16){ base=vec3(0.13); metal=1.; rough=0.5; if(r<0.06) { base=vec3(0.2,0.02,0.02); metal=0.; } }
    return; }
  if(uPal==2){ // Цитадель: белый мрамор с прожилками, золото
    float vein=pow(abs(sin(p.x*40.+fbm(p.xyz*8.)*6.)),12.);
    base=vec3(0.86,0.84,0.80)*(0.85+0.2*st)-vec3(0.25,0.22,0.18)*vein*0.6; rough=0.25;
    if(e<0.118){ brass(p,base,rough); base*=vec3(1.05,1.0,0.8); metal=1.; rough*=0.6; }
    if(r<0.16){ brass(p,base,rough); metal=1.; rough*=0.5;
      if(r<0.128){ base=vec3(0.92,0.90,0.86); metal=0.; rough=0.2; float star=1.-smoothstep(0.003,0.006,min(a,b)); if(star>.5){ brass(p,base,rough); metal=1.; } } }
    return; }
  vec3 paper= k==0? vec3(0.13,0.24,0.25) : k==1? vec3(0.30,0.10,0.09) : k==2? vec3(0.27,0.23,0.12) : vec3(0.13,0.17,0.27);
  base=paper*(0.70+0.6*st);
  float dm=abs(sin(r*55.)*sin(min(a,b)*55.)); base*=1.+0.14*smoothstep(0.6,0.95,dm);
  float w=0.0035;
  float chalk=max(1.-smoothstep(w,2.*w,abs(r-0.26)), 1.-smoothstep(w,2.*w,abs(r-0.40)));
  chalk=max(chalk,(1.-smoothstep(w,2.*w,abs(a-0.09)))*step(0.18,r)*step(r,0.46));
  base=mix(base,vec3(0.80,0.82,0.78),chalk*0.35*smoothstep(0.3,0.6,fbm(p.xyz*30.)));
  base*=mix(0.5,1.,smoothstep(0.115,0.20,e));
  if(e<0.118){ float gr=fbm(vec3(alongEdge(p)*60.,e*300.,1.)); base=vec3(0.20,0.11,0.055)*(0.65+0.7*gr); rough=0.42;
    if(abs(e-0.075)<0.0065){ brass(p,base,rough); metal=1.; } }
  if(r<0.16){
    if(r>0.128){ brass(p,base,rough); metal=1.; }
    else{ base=vec3(0.10,0.16,0.30)*(0.8+0.4*fbm(p.xyz*60.)); rough=0.12; metal=0.;
      float star=1.-smoothstep(0.003,0.006,min(a,b)), ring=1.-smoothstep(0.003,0.006,abs(r-0.08));
      if(max(star,ring)>0.5){ brass(p,base,rough); metal=1.; } } }
}
float guardShadow(vec4 P, vec4 Lw){
  float dl=acosh(max(-md(P,Lw),1.)); vec4 tl=tp(Lw,P); float s=1.;
  for(int j=0;j<NO;j++){ if(j>=uNO) break; int kd=okind(j); if(kd!=1&&kd!=8) continue;
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
  traceObjects(p0,v0);
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
            if(uGlass>.5) glassCross(p,v,t,thr,acc,uLampC,litC); }
        }
      }
      if(!any) break;
    }
    gW[0]=false; gW[1]=false; gW[2]=false;
    float d0=map(p);
    for(int q=0;q<3;q++){ float df=asinh(-md(p,uF[q])); if(df<d0+0.02) gW[q]=roomKey(nkey(uF[q]))<0; }
    d=map(p);
    if(t+d>=gTO){ ohit=true; break; }
    if(d<3e-4*(1.+t)){hit=true;break;}
    float st=min(d,max(asinh(-md(p,uM[0])),0.)+1e-3);
    float sl=sinh(acosh(max(p.w,1.)));
    float dust=0.65+0.7*vnoise(p.xyz*6.+vec3(0.,uTime*0.04,0.));               // пыль в луче света
    acc+=thr*uLampC*litC*(0.013/(0.015+sl*sl))*dust*min(st,0.25)*exp(-t/uFog);
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
    if(id==3) sc=lampShade(n,v,uLampC,lit);
    else{
      float ao=calcAO(p,n);
      if(lit>0.&&room>=0){ vec4 P=cosh(t)*p0+sinh(t)*v0; att*=guardShadow(P,uRC[room]); }
      vec3 base; float metal=1., rough;
      if(id==1){ brass(p,base,rough); float u=alongEdge(p); float gb=abs(fract(u*13.)-0.5)/13.; base*=mix(0.40,1.,smoothstep(0.002,0.006,gb));
        if(uPal==1){ base=vec3(0.30,0.29,0.28)*mix(0.5,1.,smoothstep(0.002,0.006,gb)); rough=0.5; } }
      else if(id==2){ base=vec3(0.78,0.80,0.84); rough=0.16+0.2*fbm(p.xyz*25.); }
      else wallMat(p,room,base,metal,rough);
      sc=brdf(base,metal,rough,n,v,L,p)*uLampC*att*mix(0.5,1.,ao)+ambEnv(n,v,L,uLampC,att,base,metal,rough,ao);
      // «выпрямление»: рёбра раскаляются белым, стены выцветают
      if(uStraight>0.){ if(id==1) sc+=vec3(1.0,0.96,0.88)*uStraight*1.6*(0.55+0.45*sin(uTime*9.+alongEdge(p)*40.)); else sc=mix(sc,vec3(0.8,0.82,0.86)*(0.3+0.7*lit),0.35*uStraight); }
    }
    col=mix(FOG,sc,exp(-t/uFog));
  } else if(ohit){
    tHit=gTO; t=gTO;
    col=mix(FOG,shadeObject(p0,v0,uLampC),exp(-t/uFog));
  }
  col=overlays(col,tHit,p0,v0);
  fragColor=outc(acc+thr*col, tHit<1e8? tHit : 60.);
}`;

// ───────── шейдер башни на орисферах ─────────
const FS_HS=HEAD+`
uniform float uS; uniform vec2 uCell;
const float LN2=0.6931471806;
const vec3 FOG=vec3(0.030,0.030,0.058);
vec2 gCell;
void parab(inout vec4 x, float a, float b){ float w=x.w-x.z, u=x.w+x.z; float x1=x.x+a*w, x2=x.y+b*w;
  u+=2.*a*x.x+2.*b*x.y+(a*a+b*b)*w; x=vec4(x1,x2,(u-w)*.5,(u+w)*.5); }
void dil(inout vec4 x, float a){ float c=cosh(a), s=sinh(a); x.zw=vec2(c*x.z+s*x.w, s*x.z+c*x.w); }
vec4 fromHS(vec3 q){ float w=1./q.z; float u=dot(q,q)/q.z; return vec4(q.x*w,q.y*w,(u-w)*.5,(u+w)*.5); }
float map(vec4 p){
  float w=p.w-p.z, Z=1./w, X=p.x*Z, Y=p.y*Z, lz=log(Z);
  vec2 q=vec2(X,Y);
  vec2 c=vec2(X<uS*.5?0.:uS, Y<uS*.5?0.:uS);
  float d=asinh(length(q-c)*w)-uTube*1.25; gId=1;
  float bx=min(X,uS-X), by=min(Y,uS-Y);
  float a1=asinh(min(bx,by)*w);
  float b1=sqrt(lz*lz+a1*a1)-uTube; if(b1<d){d=b1;gId=2;}
  vec2 par=mod(gCell,2.);
  float a2=asinh(min(abs(X-par.x*uS),abs(Y-par.y*uS))*w), dc=lz-LN2;
  float b2=sqrt(dc*dc+a2*a2)-uTube; if(b2<d){d=b2;gId=2;}
  vec3 lc=vec3(uS*.5,uS*.5,1.41421356);
  vec3 dq=vec3(q,Z)-lc;
  float dl=acosh(1.+dot(dq,dq)/(2.*Z*lc.z))-0.05; if(dl<d){d=dl;gId=3;}
  return d;
}` + NORMAL + LIGHT + OBJ_SDF + OBJ_H + `
void glassFloor(vec4 p, vec4 v, inout vec3 thr, inout vec3 acc, float t){
  if(uGlass<.5) return;
  vec2 par=mod(gCell,2.); bool odd=mod(par.x+par.y,2.)>.5;
  float fr=fresnel(abs(md(v,tp(vec4(0,0,1,1),p)))); float fg=exp(-t/uFog);
  vec3 tint=odd? vec3(0.78,0.86,0.97): vec3(0.98,0.84,0.62);
  acc+=thr*fg*fr*tint*0.2; thr*=mix(vec3(1.),tint,0.28)*(1.-0.35*fr);
}
void glassWall(vec4 p, vec4 v, vec4 nn, inout vec3 thr, inout vec3 acc, float t){
  if(uGlass<.5) return;
  float fr=fresnel(abs(md(v,tp(nn,p)))); float fg=exp(-t/uFog);
  acc+=thr*fg*fr*vec3(0.30,0.48,0.85)*0.16; thr*=vec3(0.95,0.96,0.985)*(1.-0.35*fr);
}
void foldH(inout vec4 p, inout vec4 v, inout vec3 thr, inout vec3 acc, float t){
  for(int it=0;it<12;it++){
    float w=p.w-p.z, Z=1./w;
    if(Z>=2.){ dil(p,-LN2); dil(v,-LN2); vec2 par=mod(gCell,2.); gCell=floor(gCell*.5);
      parab(p,par.x*uS*.5,par.y*uS*.5); parab(v,par.x*uS*.5,par.y*uS*.5); glassFloor(p,v,thr,acc,t); continue; }
    if(Z<1.){ glassFloor(p,v,thr,acc,t); dil(p,LN2); dil(v,LN2); gCell*=2.; continue; }
    float X=p.x*Z, Y=p.y*Z;
    if(X>=uS){ parab(p,-uS,0.); parab(v,-uS,0.); gCell.x+=1.; glassWall(p,v,vec4(1,0,0,0),thr,acc,t); continue; }
    if(X<0.){ glassWall(p,v,vec4(1,0,0,0),thr,acc,t); parab(p,uS,0.); parab(v,uS,0.); gCell.x-=1.; continue; }
    if(Y>=uS){ parab(p,0.,-uS); parab(v,0.,-uS); gCell.y+=1.; glassWall(p,v,vec4(0,1,0,0),thr,acc,t); continue; }
    if(Y<0.){ glassWall(p,v,vec4(0,1,0,0),thr,acc,t); parab(p,0.,uS); parab(v,0.,uS); gCell.y-=1.; continue; }
    break;
  }
  gCell=mod(gCell,1024.);
}
void main(){
  vec2 uv=(2.*gl_FragCoord.xy-uRes)/uRes.y;
  vec3 dr=normalize(vec3(uv*uTanFov,1.));
  vec4 p=uCam[3], v=uCam[0]*dr.x+uCam[1]*dr.y+uCam[2]*dr.z;
  vec4 p0=p, v0=v;
  traceObjects(p0,v0);
  gCell=uCell;
  vec3 thr=vec3(1.), acc=vec3(0.); float t=0., d=0.; bool hit=false, ohit=false;
  for(int i=0;i<180;i++){
    foldH(p,v,thr,acc,t);
    d=map(p);
    if(t+d>=gTO){ ohit=true; break; }
    if(d<3e-4*(1.+t)){hit=true;break;}
    float lz=log(1./(p.w-p.z));
    float s=min(d,min(lz,LN2-lz)+0.015);
    adv(p,v,s); t+=s;
    if(t>14.||thr.g<0.02) break;
  }
  vec3 col=FOG; float tHit=1e9;
  vec3 lamp=vec3(1.0,0.76,0.46);
  if(hit){
    tHit=t;
    int id=gId; vec4 n=calcN(p,d);
    vec3 sc;
    if(id==3) sc=lampGlobe(n,v,lamp,1.,normalize(n.xyz));
    else{
      vec4 Lp=fromHS(vec3(uS*.5,uS*.5,1.41421356));
      vec4 L=tp(Lp,p); float sr=sinh(acosh(max(-md(p,Lp),1.)));
      float att=1.0/(0.2+sr*sr);
      vec3 base; float rough, metal=1.;
      if(id==1){ brass(p,base,rough); } else { brass(p,base,rough); base*=0.7; rough=min(rough+0.2,1.); }
      sc=brdf(base,metal,rough,n,v,L,p)*lamp*att+ambEnv(n,v,L,lamp,att,base,metal,rough,1.);
    }
    col=mix(FOG,sc,exp(-t/uFog));
  } else if(ohit){
    tHit=gTO; t=gTO; col=mix(FOG,shadeObject(p0,v0,lamp),exp(-t/uFog));
  }
  col=overlays(col,tHit,p0,v0);
  fragColor=outc(acc+thr*col, tHit<1e8? tHit : 60.);
}`;

// ───────── шейдер равнины {5,4} ─────────
const FS_PL=HEAD+`
uniform vec4 uM[3]; uniform vec4 uE1; uniform vec4 uE2; uniform float uCamPar; uniform float uLampH; uniform mat4 uGW;
const vec3 FOG=vec3(0.20,0.21,0.30);
const vec3 SUN=vec3(0.62,-0.55,0.16);
// Небо Равнины: точки абсолюта (идеальные точки) в мировых координатах — поэтому небо не «прыгает» на сгибах.
vec3 skyCol(vec3 w,float sv){
  vec3 S=normalize(SUN); float h=clamp(sv,-0.2,1.);
  vec3 hor=vec3(0.80,0.42,0.26), mid=vec3(0.26,0.15,0.28), zen=vec3(0.025,0.035,0.10);
  vec3 c=mix(hor,mid,smoothstep(-0.02,0.16,h)); c=mix(c,zen,smoothstep(0.14,0.7,h));
  float sd=max(dot(w,S),0.);
  c+=vec3(1.0,0.66,0.36)*(pow(sd,6.)*0.35+pow(sd,60.)*1.2)*smoothstep(-0.1,0.1,h+0.05);
  c+=vec3(1.4,1.15,0.85)*smoothstep(0.9975,0.999,sd)*3.;                       // диск светила
  // облака: растянутые по горизонтали мазки, подсвечены со стороны светила
  vec2 cp=w.xy/(abs(w.z)+0.22)*2.6;
  float n=fbm(vec3(cp*vec2(1.1,2.4),1.7)), n2=fbm(vec3(cp*3.1,4.2));
  float dens=smoothstep(0.42,0.66,n*0.75+n2*0.35)*smoothstep(0.0,0.06,h)*(1.-smoothstep(0.5,0.85,h));
  vec3 cc=mix(vec3(0.10,0.07,0.13),vec3(1.0,0.55,0.32),pow(sd,2.)*0.9+0.1*n)*(0.6+0.6*n2);
  c=mix(c,cc,dens*0.92);
  // звёзды в зените
  vec3 sp=floor(w*260.); float st=step(0.9975,fract(sin(dot(sp,vec3(12.9898,78.233,37.719)))*43758.5453));
  c+=vec3(0.9,0.95,1.1)*st*smoothstep(0.35,0.8,h)*(1.-dens)*0.8;
  return c;
}
float map(vec4 p){
  float d=asinh(p.z); gId=0;
  float a=md(p,uE1), b=md(p,uE2);
  float dp=asinh(sqrt(a*a+b*b))-uTube; if(dp<d){d=dp;gId=1;}
  vec4 C=vec4(0.,0.,sinh(uLampH),cosh(uLampH));
  float dl=acosh(max(-md(p,C),1.))-0.07; if(dl<d){d=dl;gId=3;}
  return d;
}` + NORMAL + LIGHT + OBJ_SDF + OBJ_H + `
void main(){
  vec2 uv=(2.*gl_FragCoord.xy-uRes)/uRes.y;
  vec3 dr=normalize(vec3(uv*uTanFov,1.));
  vec4 p=uCam[3], v=uCam[0]*dr.x+uCam[1]*dr.y+uCam[2]*dr.z;
  vec4 p0=p, v0=v;
  traceObjects(p0,v0);
  float t=0., d=0.; int par=0; bool hit=false, ohit=false;
  for(int i=0;i<170;i++){
    for(int it=0;it<16;it++){
      bool any=false;
      for(int k=0;k<3;k++){ float s=md(p,uM[k]);
        if(s>0.){ p-=2.*s*uM[k]; v-=2.*md(v,uM[k])*uM[k]; any=true; if(k==0) par++; } }
      if(!any) break;
    }
    d=map(p);
    if(t+d>=gTO){ ohit=true; break; }
    if(d<3e-4*(1.+t)){hit=true;break;}
    adv(p,v,d); t+=d;
    if(t>18.) break;
  }
  vec4 up=tp(vec4(0,0,1,0),p);
  float sv=md(v,up);
  vec4 wq=uGW*(p0+v0); vec3 w=normalize(wq.xyz);                 // идеальная точка луча в мире
  vec4 up0=tp(vec4(0,0,1,0),p0); float sv0=md(v0,up0);
  vec3 sky=skyCol(w,sv0);
  vec3 haze=skyCol(w,0.02)*0.85;                                   // воздушная перспектива — цвет неба у горизонта
  vec3 col=sky; float tHit=1e9;
  vec3 lamp=vec3(1.0,0.80,0.55);
  if(hit){
    tHit=t;
    int id=gId; vec4 n=calcN(p,d);
    vec4 C=vec4(0.,0.,sinh(uLampH),cosh(uLampH));
    vec4 L=tp(C,p); float sr=sinh(acosh(max(-md(p,C),1.)));
    float att=0.9/(0.15+sr*sr);
    float skyl=0.35+0.65*max(md(n,up),0.);
    vec3 sc;
    if(id==3) sc=lampGlobe(n,v,lamp,1.,normalize(n.xyz));
    else if(id==1){ vec3 base; float rough; brass(p,base,rough);
      sc=brdf(base,1.,rough,n,v,L,p)*lamp*att+ambEnv(n,v,L,lamp,att,base,1.,rough,1.)+base*0.10*skyl; }
    else{
      bool odd=((par+int(uCamPar))%2)==1;
      vec3 base=odd? vec3(0.16,0.25,0.36): vec3(0.74,0.64,0.50);
      float g1=fbm(p.xyz*12.), g2=fbm(p.xyz*48.+3.);
      base*=0.78+0.38*g1;
      if(!odd){ vec2 bq=p.xy*38.; bq.x+=0.5*floor(bq.y); vec2 bf=abs(fract(bq)-.5);          // брусчатка
        base*=mix(0.62,1.,smoothstep(0.015,0.06,0.5-max(bf.x,bf.y)))*(0.9+0.2*fract(sin(dot(floor(bq),vec2(7.1,3.7)))*91.3));
        base=mix(base,vec3(0.36,0.42,0.22),smoothstep(0.55,0.8,g2)*0.45); }                 // мох между камнями
      else { base=mix(base,vec3(0.32,0.40,0.50),smoothstep(0.6,0.9,g2)*0.3); }
      float e=asinh(abs(md(p,uM[0])));
      float lw=0.010+0.0025*t;
      base=mix(base,vec3(0.07,0.06,0.05),1.-smoothstep(lw,lw*1.8,e));
      sc=base*(0.30*skyl*vec3(0.85,0.82,1.0)+max(md(n,L),0.)*att*lamp*0.9)+base*vec3(1.0,0.7,0.5)*0.06;
    }
    col=mix(haze,sc,exp(-t/uFog));
  } else if(ohit){
    tHit=gTO; t=gTO; col=mix(haze,shadeObject(p0,v0,lamp)+vec3(0.05,0.05,0.07),exp(-t/uFog));
  }
  col=overlays(col,tHit,p0,v0);
  fragColor=outc(col, tHit<1e8? tHit : 60.);
}`;

// ───────── шейдер евклидова города (пролог) ─────────
const FS_FL=HEAD+`
uniform float uBall;
#define NOE 12
uniform vec4 uO[NOE]; uniform vec4 uOR[NOE]; uniform vec4 uOU[NOE]; uniform vec4 uOD[NOE]; uniform vec4 uOK[NOE]; uniform int uNO;
const vec3 FOG=vec3(0.035,0.04,0.07);
int gIdE;
float mapE(vec3 p){ vec3 f=fract(p), m=min(f,1.-f);
  float d=min(min(length(m.xy),length(m.yz)),length(m.xz))-uTube; gIdE=1;
  float db=length(m)-uBall; if(db<d){d=db;gIdE=2;}
  float dl=length(f-.5)-0.055; if(dl<d){d=dl;gIdE=3;}
  return d; }
` + LIGHT + OBJ_SDF + `
void main(){
  vec2 uv=(2.*gl_FragCoord.xy-uRes)/uRes.y;
  vec3 dr=normalize(vec3(uv*uTanFov,1.));
  vec3 p0=uCam[3].xyz, v=normalize(uCam[0].xyz*dr.x+uCam[1].xyz*dr.y+uCam[2].xyz*dr.z);
  // объекты
  float tO=1e9; int iO=-1;
  for(int j=0;j<NOE;j++){ if(j>=uNO) break;
    vec3 C=uO[j].xyz; float R=uOK[j].y; vec3 oc=p0-C; float b=dot(oc,v), c=dot(oc,oc)-R*R, h=b*b-c; if(h<0.) continue;
    h=sqrt(h); float t0=max(-b-h,0.), t1=-b+h; if(t1<0.||t0>=tO) continue;
    int kind=int(uOK[j].x+.5); float tt=t0; gPar=uOK[j].z;
    for(int s=0;s<48;s++){ vec3 X=p0+v*tt-C; vec3 q=vec3(dot(X,uOR[j].xyz),dot(X,uOU[j].xyz),dot(X,uOD[j].xyz));
      int m; float dd=objSDF(kind,q,0.,0,m); if(dd<2.5e-4){ if(tt<tO){tO=tt;iO=j;} break; } tt+=dd; if(tt>t1) break; }
  }
  vec3 p=p0; vec3 thr=vec3(1.), acc=vec3(0.); float t=0., d=0.; bool hit=false, ohit=false;
  vec3 cell=floor(p);
  for(int i=0;i<160;i++){
    d=mapE(p);
    if(t+d>=tO){ohit=true;break;}
    if(d<3e-4*(1.+t)){hit=true;break;}
    p+=v*d; t+=d;
    vec3 nc=floor(p);
    if(nc!=cell){ vec3 ch=abs(nc-cell);
      for(int a=0;a<3;a++) if(ch[a]>0.5){ float fr=fresnel(abs(v[a])); float fg=exp(-t/uFog);
        acc+=thr*fg*fr*vec3(0.30,0.48,0.85)*0.20; thr*=vec3(0.93,0.95,0.98)*(1.-0.35*fr); }
      cell=nc; }
    if(t>15.||thr.g<0.02) break;
  }
  vec3 col=FOG; float tHit=60.;
  vec3 lamp=vec3(1.0,0.86,0.66);
  if(hit){
    tHit=t; int id=gIdE; const float e=1e-3;
    vec3 n=normalize(vec3(mapE(p+vec3(e,0,0))-d,mapE(p+vec3(0,e,0))-d,mapE(p+vec3(0,0,e))-d));
    vec3 c=floor(p)+.5; vec3 L=normalize(c-p); float r=length(c-p); float att=1.5/(0.22+r*r);
    vec3 sc;
    if(id==3) sc=lampGlobe(vec4(n,0.),vec4(v,0.),lamp,1.,n);
    else{ vec3 base; float rough; brass(vec4(p,1.),base,rough); if(id==2){ base=vec3(0.82,0.83,0.86); rough=0.2; }
      float dif=max(dot(n,L),0.); vec3 hv=normalize(L-v); float sp=pow(max(dot(n,hv),0.),mix(80.,10.,rough));
      base*=0.55; sc=base*(0.03+dif*att*lamp*0.32)+sp*att*lamp*base*0.3+base*vec3(0.03,0.04,0.07); }
    col=mix(FOG,sc,exp(-t/uFog));
  } else if(ohit){
    tHit=tO; vec3 X=p0+v*tO; int j=iO; int kind=int(uOK[j].x+.5); vec3 C=uO[j].xyz;
    vec3 q=vec3(dot(X-C,uOR[j].xyz),dot(X-C,uOU[j].xyz),dot(X-C,uOD[j].xyz));
    int mm; const vec2 h=vec2(1.,-1.)*0.0006; gPar=uOK[j].z;
    vec3 nq=normalize(h.xyy*objSDF(kind,q+h.xyy,0.,0,mm)+h.yyx*objSDF(kind,q+h.yyx,0.,0,mm)+h.yxy*objSDF(kind,q+h.yxy,0.,0,mm)+h.xxx*objSDF(kind,q+h.xxx,0.,0,mm));
    objSDF(kind,q,0.,0,mm);
    vec3 n=normalize(nq.x*uOR[j].xyz+nq.y*uOU[j].xyz+nq.z*uOD[j].xyz);
    vec3 c=floor(X)+.5; vec3 L=normalize(c-X); float r=length(c-X); float att=1.5/(0.22+r*r);
    float f=clamp(-dot(n,v),0.,1.);
    vec3 base, emis; float metal, rough;
    objMat(mm,kind,0,uOK[j].z,0.,q,f,vec4(X,1.),base,metal,rough,emis);
    vec3 hv=normalize(L-v); float sp=pow(max(dot(n,hv),0.),mix(90.,8.,rough));
    vec3 sc=base*(0.06+max(dot(n,L),0.)*att*lamp*0.7)*(1.-metal*0.6)+sp*att*lamp*mix(vec3(0.04),base,metal)*2.+emis+vec3(0.25,0.35,0.6)*pow(1.-f,4.)*0.2;
    col=mix(FOG,sc,exp(-tO/uFog));
  }
  fragColor=outc(acc+thr*col,tHit);
}`;

const PROG={};
for(const [k,fs] of [['rooms',FS_RM],['house',FS_HS],['plane',FS_PL],['flat',FS_FL]]){
  try{PROG[k]=program(gl,fs);}catch(e){console.error('shader '+k,e);PROG[k]=null;PROG[k+'_err']=e;}}

// ───────── звук ─────────
const AU={ctx:null,on:true,drone:null,
  init(){if(this.ctx)return;try{this.ctx=new (window.AudioContext||window.webkitAudioContext)();}catch(_){return;}
    const c=this.ctx,gn=c.createGain();gn.gain.value=0.0;gn.connect(c.destination);
    const o1=c.createOscillator(),o2=c.createOscillator();o1.frequency.value=110;o2.frequency.value=165;
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
  // тема Николая: фраза, которая не возвращается в тонику (концепт, §10)
  nikolai(){[392,440,523,494,587,554].forEach((f,i)=>setTimeout(()=>this.tone(f,0.7,'sine',0.035),i*170));},
  mirror(){this.tone(990,0.4,'triangle',0.05,1480);this.tone(1485,0.4,'sine',0.03,990);},
  setDrone(alert,active){if(!this.drone)return;const t=this.ctx.currentTime;
    this.drone.gn.gain.setTargetAtTime(active&&this.on?0.018:0,t,0.3);
    this.drone.o2.frequency.setTargetAtTime(165*(1+0.045*alert),t,0.2);},
};

// ═══════════════ адаптеры геометрий ═══════════════
const LN2=Math.LN2;
const BOUND={21:0.06,20:0.1,19:0.1,18:0.09,17:0.16,1:0.16,2:0.04,3:0.095,4:0.07,5:0.15,7:0.05,8:0.16,9:0.27,10:0.16,12:0.08,13:0.07,15:0.11,16:0.45};
// базовые операции в пространстве Лобачевского
const HYP={dist:hyperbolicDistance,dirTo,advance:(p,u,s)=>advancePose(p,u,s)};

// ───────── соты из многогранников ─────────
function makeRooms(L){
  const p=L.poly[0],r=L.poly[1],g=p===5?GEO.dodeca:GEO.cubes;
  let U;if(p===5){const f=(1+Math.sqrt(5))/2;U=[];for(const a of [1,-1])for(const b of [1,-1])U.push([0,a,b*f],[a,b*f,0],[b*f,0,a]);}
  else U=[[1,0,0],[0,1,0],[0,0,1],[-1,0,0],[0,-1,0],[0,0,-1]];
  U=U.map(u=>{const l=Math.hypot(...u);return u.map(x=>x/l);});
  const c5=p===5?1/Math.sqrt(5):0,ch2=(1+Math.cos(2*Math.PI/r))/(1-c5),CHD=Math.sqrt(ch2),SHD=Math.sqrt(ch2-1);
  const FACES=U.map(u=>[CHD*u[0],CHD*u[1],CHD*u[2],SHD]),RF=FACES.map(refl),DELTA=Math.acosh(CHD);
  const ANCH=[[0.42,0.05,-0.10,1],[-0.10,0.40,0.15,1],[0.05,-0.12,0.44,1],[-0.30,-0.25,-0.20,1]].map(normalizePoint);
  const R=[];const find=c=>R.findIndex(q=>-md(q.c,c)<1.002);
  for(const [id,from,dir,name,lit] of L.rooms){let T;
    if(!from)T=I4();else{const Tf=R.find(q=>q.id===from).T,tg=far(dir);let best=null;
      for(let k=0;k<FACES.length;k++){const T2=mul(Tf,RF[k]),c2=apply(T2,O);if(find(c2)>=0)continue;const s=-md(c2,tg);if(!best||s<best.s)best={s,T2};}
      T=best.T2;}
    R.push({id,name,T,c:apply(T,O),lit0:!!lit});}
  const RI=id=>R.findIndex(q=>q.id===id);
  const seals=new Set((L.seal||[]).map(([a,b])=>[RI(a),RI(b)].sort().join('-')));
  const sealed=(a,b)=>seals.has([a,b].sort().join('-'));
  const adjacent=(i,j)=>i!==j&&Math.abs(hyperbolicDistance(R[i].c,R[j].c)-2*DELTA)<0.01;
  const buildNb=()=>R.forEach((q,i)=>{q.nb=[];R.forEach((w,j)=>{if(adjacent(i,j)&&!sealed(i,j))q.nb.push(j);});});
  buildNb();R.forEach(q=>{q.key=ANCH.map(a=>-md(q.c,a));});
  // вершины и рёбра базового многогранника — для чертежа в Линзе (модель Кэли — Клейна)
  const VERTS=[],EDGES=[];{const nF=FACES.length;
    for(let a=0;a<nF;a++)for(let b=a+1;b<nF;b++)for(let c=b+1;c<nF;c++){let x;try{x=foot([FACES[a],FACES[b],FACES[c]]);}catch(_){continue;}
      if(!(md(x,x)<-0.5))continue;if(FACES.some(F=>md(x,F)>1e-6))continue;if(VERTS.some(v=>-md(v,x)<1+1e-9))continue;VERTS.push(x);}
    const on=VERTS.map(v=>FACES.map((F,k)=>Math.abs(md(v,F))<1e-6?k:-1).filter(k=>k>=0));
    for(let i=0;i<VERTS.length;i++)for(let j=i+1;j<VERTS.length;j++)if(on[i].filter(k=>on[j].includes(k)).length>=2)EDGES.push([i,j]);}
  const roomAt=c=>{for(let i=0;i<R.length;i++)if(-md(R[i].c,c)<1.002)return i;return -1;};
  function roomFold(x){let y=x.slice(),T=I4();
    for(let it=0;it<48;it++){let bk=-1,bs=1e-12;for(let k=0;k<FACES.length;k++){const s=md(y,FACES[k]);if(s>bs){bs=s;bk=k;}}
      if(bk<0)break;y=apply(RF[bk],y);T=mul(T,RF[bk]);}
    return {y,T};}
  const roomOf=x=>roomAt(apply(roomFold(x).T,O));
  const radii={tube:0.04,ball:p===5?0.085:0.075};
  function sdf(x,lampR,glassSolid){const f=roomFold(x);let z=f.y,W=f.T;
    const cur=roomAt(apply(W,O));
    for(let it=0;it<12;it++){let any=false;for(let k=1;k<4;k++)if(md(z,g.M[k])>0){z=apply(g.R[k],z);W=mul(W,g.R[k]);any=true;}if(!any)break;}
    let d=roomsObstacleMap(z,g,{...radii,lamp:lampR??0.055});
    for(let i=0;i<3;i++){const dF=Math.asinh(-md(z,FACES[i]));if(dF<d+0.02){const ni=roomAt(apply(W,apply(RF[i],O)));
      if(ni<0||(glassSolid&&sealed(cur,ni)))d=Math.min(d,dF);}}
    return d;}
  const faceCenter=(i,j)=>mid(R[i].c,R[j].c);
  const beyond=(i,j,s)=>{const c=R[i].c;return advancePose(c,dirTo(c,R[j].c),DELTA+s).p;};
  function roomPoint(b,fin,fout,rr){const c=R[b].c,din=dirTo(c,fin),dout=dirTo(c,fout),dd=md(din,dout);
    const w=Math.abs(dd)>0.9?perpAt(c,din):tangent(din.map((x,i)=>x+dout[i]),c);return advancePose(c,w,rr??0.33).p;}
  function bfs(a,b){if(a===b)return [a];const prev=new Map([[a,-1]]),q=[a];
    while(q.length){const x=q.shift();for(const y of R[x].nb)if(!prev.has(y)){prev.set(y,x);if(y===b){const pth=[b];let z=b;while(prev.get(z)>=0){z=prev.get(z);pth.unshift(z);}return pth;}q.push(y);}}
    return null;}
  const A={kind:'rooms',...HYP,g,ROOMS:R,RI,FACES,
    local:id=>(off)=>apply(R[RI(id)].T,normalizePoint([...off,1])),
    pointIn(id,off){return apply(R[RI(id)].T,normalizePoint([...off,1]));},
    roomOf,roomName:i=>R[i]?R[i].name:'',lights:true,
    lightF:i=>i>=0&&S.lit[i]?1:0.28,
    los(a,b){const d=hyperbolicDistance(a,b);if(d<0.05)return true;return raymarchObstacles(a,dirTo(a,b),d-0.04,x=>sdf(x,0.05,false),0.25)>=d-0.08;},
    nav(from,to){const a=roomOf(from),b=roomOf(to);if(a<0||b<0||a===b)return to;const pth=bfs(a,b);return pth&&pth.length>1?beyond(a,pth[1],0.12):to;},
    route(ids,wait){const n=ids.map(RI),W=[];
      for(let k=0;k<n.length;k++){const a=n[k],b=n[(k+1)%n.length],c=n[(k+2)%n.length];
        W.push({p:faceCenter(a,b),wait:0});W.push({p:roomPoint(b,faceCenter(a,b),faceCenter(b,c)),wait:wait??1.4});}
      return W;},
    faceCenter:(a,b)=>faceCenter(RI(a),RI(b)),
    init(){const s=RI(L.start.room),t=RI(L.start.toward);const c=R[s].c;
      const st=advancePose(c,perpAt(c,dirTo(c,R[t].c)),0.35).p;
      const cam={M:frameAt(st,dirTo(st,faceCenter(s,t))),G:I4(),par:0,cross:0};foldRooms(cam,g);return cam;},
    pos(){return normalizePoint(apply(S.c.G,col(S.c.M,3)));},
    basis(k){return apply(S.c.G,col(S.c.M,k));},
    move(dt,inp){const c=S.c,prev={M:c.M.slice(),G:c.G.slice(),par:c.par,cross:c.cross};
      if(inp.lx)rotLocal(c.M,2,0,inp.lx);if(inp.ly)rotLocal(c.M,2,1,-inp.ly);if(inp.roll)rotLocal(c.M,0,1,inp.roll*1.2*dt);
      if(inp.f)boostLocal(c.M,2,inp.f*inp.sp);if(inp.s)boostLocal(c.M,0,inp.s*inp.sp);if(inp.u)boostLocal(c.M,1,inp.u*inp.sp);
      gs(c.M);foldRooms(c,g);
      if(inp.moving){const PR_=0.07;
        for(let it=0;it<3;it++){const pp=A.pos(),d=sdf(pp,0.06,true);if(d>=PR_)break;
          const gr=[0,1,2].map(k=>{const q=advancePose(pp,tangent(A.basis(k),pp),0.01).p;return (sdf(q,0.06,true)-d)/0.01;});
          for(let k=0;k<3;k++)boostLocal(c.M,k,gr[k]*(PR_-d)*1.05);gs(c.M);foldRooms(c,g);}
        if(sdf(A.pos(),0.06,true)<PR_*0.5){c.M=prev.M;c.G=prev.G;c.par=prev.par;c.cross=prev.cross;}}},
    freeDist(p,f,max){return raymarchObstacles(p,f,max,x=>sdf(x,0.06,true),0.15);},
    blink(s){boostLocal(S.c.M,2,s);gs(S.c.M);foldRooms(S.c,g);},
    up:p=>perpAt(p,[1,0,0,0]),
    lampNear(i,p){return i>=0&&hyperbolicDistance(p,R[i].c)<0.36;},
    unseal(a,b){seals.delete([RI(a),RI(b)].sort().join('-'));buildNb();},seal(a,b){seals.add([RI(a),RI(b)].sort().join('-'));buildNb();},isSealed:(a,b)=>sealed(RI(a),RI(b)),
    roomVerts:i=>VERTS.map(v=>apply(R[i].T,v)),EDGES,roomFaces:i=>FACES.map(F=>apply(R[i].T,F)),
    render(SC,now,objs){const P=PROG.rooms;if(!P)return;gl.useProgram(P.pr);const Lc=P.loc,c=S.c,Gi=linv(c.G);
      const f1=(n,v)=>{if(Lc[n]!=null)gl.uniform1f(Lc[n],v);},i1=(n,v)=>{if(Lc[n]!=null)gl.uniform1i(Lc[n],v);},f4=(n,v)=>{if(Lc[n]!=null)gl.uniform4fv(Lc[n],v);};
      gl.uniform2fv(Lc.uRes,[SC.sw,SC.sh]);gl.uniformMatrix4fv(Lc.uCam,false,c.M);f1('uDirect',SC.post?0:1);
      f1('uTanFov',fovTan());f1('uFog',L.fog||6.5);f1('uGlass',1);f1('uTube',0.04);f1('uBall',radii.ball);f1('uCamPar',c.par);
      f4('uM',g.M.flat());f4('uE1',g.E1);f4('uE2',g.E2);f4('uV',g.V);f4('uF',FACES.slice(0,3).flat());f4('uP1',g.P1);
      f4('uA',ANCH.map(a=>apply(Gi,a)).flat());f4('uK',R.map(q=>q.key).flat());f4('uRC',R.map(q=>apply(Gi,q.c)).flat());
      if(Lc.uLit!=null)gl.uniform1fv(Lc.uLit,S.lit.map(x=>x?1:0));i1('uNK',R.length);
      f1('uStraight',S.straight||0);i1('uPal',L.pal||0);if(Lc.uLampC!=null)gl.uniform3fv(Lc.uLampC,L.lamp||[1.0,0.68,0.36]);
      setObjects(Lc,objs,x=>apply(Gi,x),now);gl.drawArrays(gl.TRIANGLES,0,3);},
  };
  return A;
}

// ───────── башня на орисферах ─────────
function makeHouse(L){
  const HSZ=1.0;
  const camM=c=>{const cx=Math.floor(c.X),cy=Math.floor(c.Y);return mul(mul(parabM(c.X-cx,c.Y-cy),boostZ(c.h)),rotYP(c.yaw,c.pitch));};
  const Fm=c=>mul(parabM(-Math.floor(c.X),-Math.floor(c.Y)),boostZ(-c.L*LN2));
  const Finv=c=>mul(boostZ(c.L*LN2),parabM(Math.floor(c.X),Math.floor(c.Y)));
  const hsAbs=(X,Y,Lf,h)=>{const f=Math.pow(2,Lf);return fromHS([X*f,Y*f,Math.exp(h)*f]);};
  const floorOf=p=>{const z=toHS(p)[2];return Math.floor(Math.log2(z)+1e-9);};
  const A={kind:'house',L,...HYP,
    pointAt:(X,Y,Lf,h)=>hsAbs(X,Y,Lf,h??0.35),
    roomOf:p=>floorOf(p)+100,roomName:i=>L.floorNames[i-100]||('Этаж '+(i-100)),lights:false,
    lightF:()=>0.8,los:()=>true,nav:(a,b)=>b,
    route(pts,wait){return pts.map(q=>({p:hsAbs(q[0],q[1],q[2],q[3]??0.33),wait:wait??1.2}));},
    init(){return {X:L.start[0],Y:L.start[1],L:L.start[2],h:0.26,yaw:Math.PI/2,pitch:0.15};},
    pos(){return normalizePoint(apply(Finv(S.c),col(camM(S.c),3)));},
    basis(k){return apply(Finv(S.c),col(camM(S.c),k));},
    move(dt,inp){const c=S.c;c.yaw-=inp.lx;c.pitch=clamp(c.pitch-inp.ly,-1.5,1.5);
      const cy=Math.cos(c.yaw),sy=Math.sin(c.yaw),dx=inp.f*cy+inp.s*sy,dy=inp.f*sy-inp.s*cy,Z=Math.exp(c.h);
      c.X+=dx*inp.sp*Z;c.Y+=dy*inp.sp*Z;c.h+=inp.u*inp.sp;
      while(c.h>=LN2){c.h-=LN2;c.X/=2;c.Y/=2;c.L++;}while(c.h<0){c.h+=LN2;c.X*=2;c.Y*=2;c.L--;}
      if(c.L<L.minFloor){c.L=L.minFloor;c.h=0.02;}if(c.L>L.maxFloor){c.L=L.maxFloor;c.h=LN2-0.02;}},
    freeDist:(p,f,max)=>max,
    blink(s){const p=advancePose(A.pos(),tangent(A.basis(2),A.pos()),s).p,q=toHS(p),c=S.c;
      let Lf=Math.floor(Math.log2(q[2]));Lf=clamp(Lf,L.minFloor,L.maxFloor);const f=Math.pow(2,Lf);
      c.L=Lf;c.X=q[0]/f;c.Y=q[1]/f;c.h=clamp(Math.log(q[2]/f),0.01,LN2-0.01);},
    up(p){const q=toHS(p);return dirTo(p,fromHS([q[0],q[1],q[2]*1.2]));},
    lampNear:()=>false,
    render(SC,now,objs){const P=PROG.house;if(!P)return;gl.useProgram(P.pr);const Lc=P.loc,c=S.c,F=Fm(c);
      const f1=(n,v)=>{if(Lc[n]!=null)gl.uniform1f(Lc[n],v);};
      gl.uniform2fv(Lc.uRes,[SC.sw,SC.sh]);gl.uniformMatrix4fv(Lc.uCam,false,camM(c));f1('uDirect',SC.post?0:1);
      f1('uTanFov',fovTan());f1('uFog',4.8);f1('uGlass',1);f1('uTube',0.022);f1('uS',HSZ);
      const m=v=>((v%1024)+1024)%1024;if(Lc.uCell!=null)gl.uniform2fv(Lc.uCell,[m(Math.floor(c.X)),m(Math.floor(c.Y))]);
      setObjects(Lc,objs,x=>apply(F,x),now);gl.drawArrays(gl.TRIANGLES,0,3);},
  };
  return A;
}

// ───────── равнина {5,4} ─────────
function makePlane(L){
  const GH=0.16; // высота центра стражей над полом
  const camAbs=c=>mul(mul(mul(c.G,c.T),boostZ(c.h)),rotYP(c.yaw,c.pitch));
  const A={kind:'plane',...HYP,
    pointAt:(r,deg,h)=>atHeight(polar(r,deg),h??GH),
    roomOf:()=>-1,roomName:()=>'',lights:false,lightF:()=>(0.3+0.45*Math.min(1,(S.c.h-0.12)/0.6))*(S.crouch?0.55:1),los:()=>true,nav:(a,b)=>b,
    constrain:p=>atHeight(footOf(p),GH),
    route(pts,wait){return pts.map(q=>({p:atHeight(polar(q[0],q[1]),GH),wait:wait??1.5}));},
    init(){const c={T:I4(),G:I4(),h:0.45,yaw:0,pitch:-0.05,par:0};return c;},
    pos(){return normalizePoint(apply(camAbs(S.c),O));},
    basis(k){return apply(camAbs(S.c),col(I4(),k));},
    move(dt,inp){const c=S.c;c.yaw-=inp.lx;c.pitch=clamp(c.pitch-inp.ly,-1.5,1.5);
      const cy=Math.cos(c.yaw),sy=Math.sin(c.yaw),dx=inp.f*cy+inp.s*sy,dy=inp.f*sy-inp.s*cy,m=Math.hypot(dx,dy);
      if(m>1e-9){const phi=Math.atan2(dy,dx);c.T=mul(c.T,mul(mul(rotZ(phi),boostX(m*inp.sp/Math.cosh(c.h))),rotZ(-phi)));}
      if(inp.u)c.h=clamp(c.h+inp.u*inp.sp,0.12,2.5);
      c.T=gsPlane(c.T);foldPlane(c);},
    freeDist:(p,f,max)=>max,
    blink(s){const c=S.c;c.T=mul(c.T,mul(mul(rotZ(c.yaw),boostX(s/Math.cosh(c.h))),rotZ(-c.yaw)));c.T=gsPlane(c.T);foldPlane(c);},
    up:p=>tangent([0,0,1,0],p),
    lampNear:()=>false,
    render(SC,now,objs){const P=PROG.plane;if(!P)return;gl.useProgram(P.pr);const Lc=P.loc,c=S.c,Gi=linv(c.G);
      const f1=(n,v)=>{if(Lc[n]!=null)gl.uniform1f(Lc[n],v);},f4=(n,v)=>{if(Lc[n]!=null)gl.uniform4fv(Lc[n],v);};
      gl.uniform2fv(Lc.uRes,[SC.sw,SC.sh]);gl.uniformMatrix4fv(Lc.uCam,false,mul(mul(c.T,boostZ(c.h)),rotYP(c.yaw,c.pitch)));f1('uDirect',SC.post?0:1);
      f1('uTanFov',fovTan());f1('uFog',8);f1('uTube',0.035);f4('uM',PL.M.flat());f4('uE1',PL.E1);f4('uE2',PL.E2);f1('uCamPar',c.par);f1('uLampH',1.1);if(Lc.uGW!=null)gl.uniformMatrix4fv(Lc.uGW,false,c.G);
      setObjects(Lc,objs,x=>apply(Gi,x),now);gl.drawArrays(gl.TRIANGLES,0,3);
      if(MAP){renderMap(c);drawMarkers(c);}},
  };
  return A;
}
const markC=document.createElement('canvas');markC.width=400;markC.height=400;markC.style.cssText='position:absolute;left:0;top:0;width:100%;height:100%;pointer-events:none';
{const mw=document.getElementById('mapwrap');mw.style.position='absolute';const m=document.getElementById('map');const holder=document.createElement('div');holder.style.cssText='position:relative';m.parentNode.insertBefore(holder,m);holder.appendChild(m);holder.appendChild(markC);}
function drawMarkers(c){const x=markC.getContext('2d');x.clearRect(0,0,400,400);
  const uT=mul(mul(c.G,c.T),rotZ(c.yaw-Math.PI/2)),Ui=linv(uT);
  for(const mk of mapMarks()){const v=apply(Ui,footOf(mk.p));const u=[v[0]/v[3],v[1]/v[3]];if(Math.hypot(...u)>0.99)continue;
    const fx=(u[0]/1.04*400+400)/2,fy=400-(u[1]/1.04*400+400)/2;
    x.fillStyle=mk.c;x.strokeStyle='#141a2e';x.lineWidth=3;x.beginPath();x.arc(fx,fy,mk.r||9,0,7);x.fill();x.stroke();}}

// ───────── евклидов город ─────────
function makeFlat(L){
  const A={kind:'flat',
    dist:(a,b)=>Math.hypot(a[0]-b[0],a[1]-b[1],a[2]-b[2]),
    dirTo:(a,b)=>{const d=[b[0]-a[0],b[1]-a[1],b[2]-a[2]],l=Math.hypot(...d)||1;return [d[0]/l,d[1]/l,d[2]/l,0];},
    advance:(p,u,s)=>({p:[p[0]+u[0]*s,p[1]+u[1]*s,p[2]+u[2]*s,1],u}),
    roomOf:p=>{const c=p.map(Math.floor);return (c[0]+50)*10000+(c[1]+50)*100+(c[2]+50);},roomName:()=>'',lights:false,lightF:()=>1,
    los:()=>true,nav:(a,b)=>b,
    init(){const M=I4();setCol(M,3,[0.5,0.5,0.1,1]);return {M,abs:[0.5,0.5,0.1]};},
    pos(){const a=S.c.abs;return [a[0],a[1],a[2],1];},
    basis(k){const M=S.c.M;return [M[k*4],M[k*4+1],M[k*4+2],0];},
    move(dt,inp){const c=S.c,M=c.M;
      if(inp.lx)rotLocal(M,2,0,inp.lx);if(inp.ly)rotLocal(M,2,1,-inp.ly);if(inp.roll)rotLocal(M,0,1,inp.roll*1.2*dt);
      const d=[0,1,2].map(i=>M[8+i]*inp.f*inp.sp+M[i]*inp.s*inp.sp+M[4+i]*inp.u*inp.sp);
      const n=[0,1,2].map(i=>c.abs[i]+d[i]);
      // не даём пройти сквозь рёбра каркаса
      const sd=q=>{const f=q.map(v=>v-Math.floor(v)),m=f.map(v=>Math.min(v,1-v));return Math.min(Math.hypot(m[0],m[1]),Math.hypot(m[1],m[2]),Math.hypot(m[0],m[2]),Math.hypot(...f.map(v=>v-0.5)))-0.1;};
      if(sd(n)>0||sd(n)>sd(c.abs))c.abs=n;
      for(let i=0;i<3;i++)M[12+i]=c.abs[i]-2*Math.floor(c.abs[i]/2);
      gsFlat(M);},
    freeDist:(p,f,max)=>max,
    blink(s){const f=A.basis(2);for(let i=0;i<3;i++)S.c.abs[i]+=f[i]*s;},
    up:()=>[0,1,0,0],lampNear:()=>false,
    render(SC,now,objs){const P=PROG.flat;if(!P)return;gl.useProgram(P.pr);const Lc=P.loc,c=S.c;
      const f1=(n,v)=>{if(Lc[n]!=null)gl.uniform1f(Lc[n],v);};
      gl.uniform2fv(Lc.uRes,[SC.sw,SC.sh]);gl.uniformMatrix4fv(Lc.uCam,false,c.M);f1('uDirect',SC.post?0:1);
      f1('uTanFov',fovTan());f1('uFog',5.5);f1('uTube',0.04);f1('uBall',0.075);f1('uTime',now/1000);
      const sh=[0,1,2].map(i=>c.abs[i]-c.M[12+i]);const O_=[],R_=[],U_=[],D_=[],K_=[];
      for(const o of objs.slice(0,12)){O_.push(o.pos[0]-sh[0],o.pos[1]-sh[1],o.pos[2]-sh[2],1);
        const D=o.dirE||[0,0,1];R_.push(D[2],0,-D[0],0);U_.push(0,1,0,0);D_.push(D[0],D[1],D[2],0);K_.push(o.kind,BOUND[o.kind]||0.08,o.par||0,0);}
      const f4=(n,v)=>{if(Lc[n]!=null&&v.length)gl.uniform4fv(Lc[n],v);};
      f4('uO',O_);f4('uOR',R_);f4('uOU',U_);f4('uOD',D_);f4('uOK',K_);if(Lc.uNO!=null)gl.uniform1i(Lc.uNO,O_.length/4);
      gl.drawArrays(gl.TRIANGLES,0,3);},
  };
  return A;
}

// общая загрузка объектов в шейдер
function setObjects(Lc,objs,toL,now){
  const O_=[],R_=[],U_=[],D_=[],K_=[],C_=[];
  for(const o of objs.slice(0,16)){const F=o.F;
    O_.push(...toL(o.pos));R_.push(...toL(col(F,0)));U_.push(...toL(col(F,1)));D_.push(...toL(col(F,2)));
    K_.push(o.kind,BOUND[o.kind]||0.08,o.par||0,(o.sl?1:0)+2*(o.lit?1:0)+4*(o.vr||0)+128*(o.walk||0));C_.push(...toL(o.light||o.pos));}
  const f4=(n,v)=>{if(Lc[n]!=null&&v.length)gl.uniform4fv(Lc[n],v);};
  f4('uO',O_);f4('uOR',R_);f4('uOU',U_);f4('uOD',D_);f4('uOK',K_);f4('uOC',C_);
  if(Lc.uNO!=null)gl.uniform1i(Lc.uNO,O_.length/4);
  if(Lc.uTime!=null)gl.uniform1f(Lc.uTime,now/1000);
  if(Lc.uLens!=null)gl.uniform1f(Lc.uLens,S.lensOn?1:0);
  if(Lc.uCosFov!=null)gl.uniform1f(Lc.uCosFov,Math.cos(FOV/2));
  if(Lc.uView!=null)gl.uniform1f(Lc.uView,VIEW);
  if(aiming&&!S.over&&!S.paused&&S.A.kind!=='flat'){const b=aimTarget();if(Lc.uMark!=null)gl.uniform4fv(Lc.uMark,toL(b.pt));if(Lc.uMarkOn!=null)gl.uniform1f(Lc.uMarkOn,b.s>0.12?1:0);}
  else if(Lc.uMarkOn!=null)gl.uniform1f(Lc.uMarkOn,0);
}

// ═══════════════ уровни ═══════════════
// предмет: {id, kind, at:позиция, name, lemma, doc, cond(S)→виден ли, var}
const LEVELS={
  prologue:()=>{const A=makeFlat();
    // линейный маршрут по оси z: Академия → коридор с патрулём → комната №7 → кабинет Ортта → улица
    const PATROL={a:[-1.5,0.45,3.5],b:[2.5,0.45,3.5],t:0};
    const it=[
      {id:'desk_exam',kind:17,pos:[0.5,0.3,1.55,1],puzzle:'square',name:'выпускной чертёж'},
      {id:'euclid',kind:2,pos:[1.5,0.72,0.5,1],lemma:'euclid'},
      {id:'rj',kind:4,pos:[2.5,0.3,0.5,1],doc:'r_journal'},
      {id:'poster',kind:4,pos:[-0.5,0.7,2.5,1],doc:'poster'},
      {id:'patrol',kind:1,pos:[...PATROL.a,1],inert:true,cond:S=>S.stage>=1&&S.stage<4},
      ...[[0.16,0.18,6.16],[0.84,0.18,6.16],[0.84,0.18,6.84],[0.16,0.18,6.84]].map((q,i)=>({id:'corner'+i,kind:13,pos:[...q,1],name:'угол '+(i+1),cond:S=>S.stage>=1})),
      {id:'ortt',kind:8,pos:[0.5,0.25,8.62,1],name:'Старший чертёжник Ортт',talk:true,cond:S=>S.stage>=1,face:[0.5,0.25,7,1]},
      {id:'exit',kind:5,pos:[0.5,0.5,10.45,1],cond:S=>S.stage>=5,exit:S=>S.stage>=5},
    ];
    let signT=0;
    return {A,items:it,guards:[],roomTitles:false,
      objectives:S=>{const n=[0,1,2,3].filter(i=>S.got['corner'+i]).length;return [
        {t:'Начертить выпускной квадрат у доски',done:S.stage>=1},
        {t:'Пройти коридор мимо патруля (Ctrl — пригнуться)',done:S.stage>=2||n>0,locked:S.stage<1},
        {t:'Обмерить углы комнаты №7 ('+n+'/4)',done:n===4,locked:S.stage<1},
        {t:'Отнести отчёт Ортту',done:S.stage>=5,locked:S.stage<4},
        {t:'Выйти из Академии',locked:S.stage<5}];},
      onSolve(pz){if(pz==='square'){S.stage=1;say('exam');setTimeout(()=>say('crouch'),9000);}},
      onPick(id){if(id.startsWith('corner')){const k=+id.slice(6),v=CH().corners[k];toast('Угол '+(k+1)+': '+v+'°');AU.tone(v===90?1200:1131,0.25,'sine',0.05);
          if([0,1,2,3].every(i=>S.got['corner'+i])){S.stage=3;say('measured');
            setTimeout(()=>{const C=CH().recordChoice;choose('vera',C.q+'<br><small style="color:var(--muted)">90° + 90° + 90° + 89° = 359°</small>',C.a,k2=>{S.flags.wrote89=k2===1;campaign.wrote89=S.flags.wrote89;saveCampaign();S.stage=4;say('report');ui.obj();lock();});},4200);}}},
      onTalk(id){if(id==='ortt'){if(S.stage<4){S.got.ortt=0;toast('Ортт занят. Сначала — обмер.');return;}
        scene([...(S.flags.wrote89?CH().report89:CH().report90),...CH().reportCommon],()=>{S.stage=5;signT=7;ui.obj();});}},
      tick(dt,p){
        // патруль ходит поперёк коридора; заметил — мягкий откат без наказания
        const P=it.find(i=>i.id==='patrol');if(S.stage>=1&&S.stage<4){PATROL.t+=dt*0.22;const w=0.5-0.5*Math.cos(PATROL.t*Math.PI);
          const pos=PATROL.a.map((v,i)=>v+(PATROL.b[i]-v)*w);const dir=Math.sin(PATROL.t*Math.PI)>=0?1:-1;P.pos=[...pos,1];P.dirE=[dir,0,0];
          const v=[p[0]-pos[0],p[1]-pos[1],p[2]-pos[2]],d=Math.hypot(...v),cosA=(v[0]*dir)/(d||1);
          const range=S.crouch?1.1:2.6;P.par=d<range+0.8&&cosA>0.6?Math.min(1,(range+0.8-d)/0.8):0;
          if(d<range&&cosA>Math.cos(35*Math.PI/180)&&!campaign.lecturer){S.c.abs=[0.5,0.5,2.3];toast('Вас заметили. Отойдите в тень и пригнитесь (Ctrl).');AU.alert();
            document.getElementById('danger').style.opacity=0.8;setTimeout(()=>document.getElementById('danger').style.opacity=0,600);}}
        // П0.9: знак Ортта виден, только если обернуться, пока Вера уходит
        if(signT>0){signT-=dt;const O_=it.find(i=>i.id==='ortt').pos,f=A.basis(2),q=[O_[0]-p[0],O_[1]-p[1],O_[2]-p[2]],l=Math.hypot(...q);
          if(!S.flags.sawSign&&l>0.5&&(f[0]*q[0]+f[1]*q[1]+f[2]*q[2])/l>0.85){S.flags.sawSign=1;campaign.sawSign=1;saveCampaign();S.subs.push({who:'—',text:CH().sign,dur:6});}}},
      start(){S.stage=0;},
      abil:{blink:false,lens:false,decoy:false}};},

  ch1:()=>{const L={poly:[5,4],pal:0,lamp:[1.0,0.68,0.36],
      rooms:[['hub',null,null,'Атриум',1],['a1','hub',[0,0.15,1],'Галерея',1],['a2','a1',[0,0.3,1],'Переход',0],['a3','a2',[0.5,0.6,1],'Комната вычеркнутого',0],
        ['b1','hub',[1,0,0.2],'Картотека',1],['b2','b1',[1,-0.2,0.4],'Дальняя картотека',0],['b3','b2',[1,-1,0.5],'Зал переписи',1],
        ['c1','hub',[-1,-0.2,-0.4],'Лестница на крышу',0],['c2','c1',[-1,-0.4,-1],'Выход на крышу',1],['s1','a1',[1,0.3,0.5],'Чертёжная',0],['s2','hub',[0,-1,0.2],'Вестибюль Архива',0]],
      seal:[['a2','a3'],['s1','a3']],start:{room:'s2',toward:'hub'}};
    const A=makeRooms(L);const P=(r,o)=>A.pointIn(r,o);
    const c2=A.ROOMS[A.RI('c2')].c,c1=A.ROOMS[A.RI('c1')].c,a3=A.ROOMS[A.RI('a3')].c;
    const it=[
      {id:'reg',kind:4,pos:P('b1',[0.18,-0.26,0.10]),doc:'reg'},{id:'card1',kind:4,pos:P('b1',[-0.22,0.22,-0.12]),doc:'card1'},
      {id:'folder',kind:4,pos:P('b2',[0.22,-0.2,0.1]),doc:'folder'},{id:'rec',kind:4,pos:P('b3',[-0.10,-0.30,0.05]),doc:'rec'},
      {id:'lock1',kind:16,pos:A.faceCenter('a2','a3'),face:a3,puzzle:'dial',name:'Замок из четырёх дисков',cond:S=>!S.flags.dialDone},
      {id:'lock2',kind:16,pos:A.faceCenter('s1','a3'),face:a3,puzzle:'dial',name:'Замок из четырёх дисков',cond:S=>!S.flags.dialDone},
      {id:'outline',kind:4,pos:P('a3',[-0.2,0.25,-0.12]),doc:'outline'},
      {id:'desk281',kind:17,pos:P('a3',[0.05,-0.36,0.10]),inert:true,puzzle:'none'},
      {id:'lens',kind:3,pos:P('a3',[0.05,-0.24,0.10]),name:'Линза Абсолюта'},
      {id:'saccheri',kind:2,pos:P('s2',[0.25,0.15,-0.10]),lemma:'saccheri'},{id:'lambert',kind:2,pos:P('s1',[-0.20,0.25,0.10]),lemma:'lambert'},
      {id:'lobachevsky',kind:2,pos:P('b2',[0.10,0.30,-0.15]),lemma:'lobachevsky'},{id:'coxeter',kind:2,pos:P('c1',[0.20,-0.25,0.20]),lemma:'coxeter'},
      {id:'sh0',kind:7,pos:P('a2',[-0.25,-0.15,0.15])},{id:'sh1',kind:7,pos:P('b1',[0.15,0.28,-0.20])},{id:'sh2',kind:7,pos:P('s2',[-0.25,-0.20,0.10])},
      {id:'r117',kind:4,pos:P('b2',[-0.25,-0.10,0.20]),doc:'r117'},{id:'r203',kind:4,pos:P('a2',[0.20,0.25,-0.10]),doc:'r203'},
      {id:'exit',kind:5,pos:advancePose(c2,dirTo(c2,c1),-0.42).p,face:c1,exit:S=>!!S.flags.lensDone}];
    const gd=[{name:'Чертёжник Орт',route:A.route(['hub','a1','s1','b1'])},{name:'Чертёжник Евтих',route:A.route(['b1','b2','b3','b2'])},
      {name:'Чертёжник Пасх',route:A.route(['a1','a2'],2.2)}];
    const tut=S=>S.flags.tutWall&&S.flags.tutGuard&&S.flags.tutOff;
    return {A,items:it,guards:gd,
      objectives:S=>[{t:'Найти реестр квартала 7-12 — Картотека',done:!!S.got.reg},
        {t:'Найти комнату 281-го — дверь за Переходом',done:!!S.flags.dialDone,locked:!S.got.reg},
        {t:'Забрать то, что оставил вычеркнутый',done:!!S.got.lens,locked:!S.flags.dialDone},
        {t:'Линза: посмотреть сквозь стену'+(S.flags.tutWall?' ✓':'')+' · на стража'+(S.flags.tutGuard?' ✓':'')+' · выключить при ясности ниже 30%'+(S.flags.tutOff?' ✓':''),done:tut(S),locked:!S.got.lens},
        {t:'Выбраться на крышу Архива',locked:!tut(S)}],
      onPick(id){if(id==='lens'){S.abil.lens=true;ui.obj();}},
      onSolve(pz){if(pz==='dial'){A.unseal('a2','a3');A.unseal('s1','a3');say('opened');}},
      onRoom(r){if(r===A.RI('a3'))say('room');
        if(r===A.RI('c1')&&S.got.lens&&!S.flags.kasselIn){S.flags.kasselIn=1;
          const K=new Guard({name:'Циркулятор Кассель',kassel:true,route:A.route(['c2','c1'],2.4)},S.guards.length);K.pos=A.ROOMS[A.RI('c2')].c.slice();K.pos=advancePose(K.pos,dirTo(K.pos,c1),0.25).p;K.dir=dirTo(K.pos,c1);
          K.state='search';K.goal=A.pos();K.alert=0.35;S.guards.push(K);say('kassel');}},
      onLensOn(){say('lensOn');},
      tick(dt,p){if(!S.got.lens)return;
        if(S.lensOn){S.flags.lensT=(S.flags.lensT||0)+dt;if(S.flags.lensT>1.2&&!S.flags.tutWall){S.flags.tutWall=1;ui.obj();}
          if(!S.flags.tutGuard){const b=[0,1,2].map(k=>A.basis(k));for(const G of S.guards){if(G.sleep)continue;const d=hyperbolicDistance(p,G.pos);if(d>4.5)continue;
            const v=dirTo(p,G.pos),z=md(v,b[2]);if(z>0.3&&Math.abs(md(v,b[0])/z)<0.45&&Math.abs(md(v,b[1])/z)<0.45){S.flags.tutGuard=1;ui.obj();break;}}}
          if(S.clar<0.35)say('clarity');}
        if(tut(S)&&!S.flags.lensDone){S.flags.lensDone=1;say('lensDone');ui.obj();}},
      onLensOff(){if(S.got.lens&&S.clar<0.31&&!S.flags.tutOff){S.flags.tutOff=1;ui.obj();}},
      afterPickLens(){say('alarm');for(const G of S.guards){if(G.sleep)continue;G.alert=Math.max(G.alert,0.3);G.state='search';G.goal=a3.slice();G.timer=0;G.scan=null;}},
      onExit(){scene(CH().roof,()=>completeChapter());},
      softCatch:true,
      restore(s2,o){if(o.flags&&o.flags.kasselIn&&s2.guards.length<o.guards.length)s2.guards.push(new Guard({name:'Циркулятор Кассель',kassel:true,route:A.route(['c2','c1'],2.4)},s2.guards.length));},
      abil:{blink:true,lens:false,decoy:false}};},

  ch2:()=>{const L={poly:[5,4],pal:1,lamp:[0.78,0.92,0.86],fog:6,
      rooms:[['cell',null,null,'Галерея камер',1],['gal1','cell',[0,0,1],'Верхняя галерея',1],['gal2','gal1',[0.4,0,1],'Сторожевой переход',0],
        ['post','gal2',[1,0,0.6],'Пост Циркулятора',1],['ev','post',[1,0.3,0],'Кладовая улик',1],['ring','gal1',[-0.6,0.5,0.6],'Кольцевой коридор',0],
        ['well','ring',[-1,0.4,0],'Колодец',0],['yard','post',[0.6,1,0.4],'Двор маятника',1],['lock','yard',[0,1,0.3],'Шлюз',1],['bath','cell',[0.5,-1,0.2],'Камера Двенадцати Стен',0]],
      start:{room:'bath',toward:'cell'}};
    const A=makeRooms(L);const P=(r,o)=>A.pointIn(r,o),R=id=>A.RI(id),C=id=>A.ROOMS[R(id)].c;
    const lk=C('lock'),yd=C('yard');
    // отражение в грани между Верхней галереей и Сторожевым переходом (симметрия соты)
    const nf=C('gal1').map((v,i)=>v-C('gal2')[i]),nn=Math.sqrt(md(nf,nf)),RFm=refl(nf.map(v=>v/nn));
    // перенос вдоль оси камеры: «выходишь в коридор — входишь в ту же камеру с другой стороны»
    const Tb=A.ROOMS[R('bath')].T,lc=apply(linv(Tb),C('cell')),u=[lc[0],lc[1],lc[2]],ul=Math.hypot(...u),uu=u.map(v=>v/ul);
    const boostDir=(w,sd)=>{const ch=Math.cosh(sd),sh=Math.sinh(sd),M=I4();for(let i=0;i<3;i++){for(let j=0;j<3;j++)M[j*4+i]=(i===j?1:0)+(ch-1)*w[i]*w[j];M[12+i]=sh*w[i];M[i*4+3]=sh*w[i];}M[15]=ch;return M;};
    const LOOP=mul(mul(Tb,boostDir(uu,-(2*Math.acosh(Math.sqrt(1/(1-1/Math.sqrt(5))))-0.32))),linv(Tb));
    const it=[{id:'compass',kind:18,pos:P('ev',[0.10,-0.26,0.10]),name:'Геодезический циркуль',lock:'gap'},
      {id:'desk_gap',kind:17,pos:P('ev',[-0.18,-0.22,-0.12]),puzzle:'gap',name:'замок-сота'},
      {id:'plate',kind:4,pos:P('ring',[0.22,-0.22,-0.1]),doc:'plate'},
      {id:'r044',kind:4,pos:P('well',[-0.2,-0.2,0.2]),doc:'r044'},{id:'r260',kind:4,pos:P('post',[0.2,0.25,0.1]),doc:'r260'},
      {id:'bolyai',kind:2,pos:P('well',[0.2,0.25,-0.1]),lemma:'bolyai'},{id:'gauss',kind:2,pos:P('ring',[-0.2,-0.25,0.15]),lemma:'gauss'},{id:'sight',kind:2,pos:P('gal2',[0.15,0.3,0.1]),lemma:'sight'},
      {id:'sh0',kind:7,pos:P('bath',[0.25,0.2,0.1])},{id:'sh1',kind:7,pos:P('yard',[-0.2,-0.25,0.15])},
      {id:'exit',kind:5,pos:advancePose(lk,dirTo(lk,yd),-0.42).p,face:yd,exit:S=>!!S.race,cond:S=>!!S.race}];
    const gd=[{name:'Циркулятор Кассель',route:A.route(['yard','post','ev','post'],1.8),kassel:true},
      {name:'Тюремщик Фавст',vr:6,route:A.route(['cell','gal1','ring','well'])},{name:'Тюремщик Лука',vr:6,route:A.route(['gal2','gal1'],2.0)},
      {name:'Тюремщик Ерм',vr:6,route:A.route(['lock','yard'],2.5)}];
    const RACE=80;
    return {A,items:it,guards:gd,
      objectives:S=>[{t:'Выбраться из камеры',done:!!S.flags.freed},
        {t:'Отпереть шкаф в Кладовой улик: чертёжный стол',done:!!S.flags.gapDone,locked:!S.flags.freed},
        {t:'Вернуть геодезический циркуль',done:!!S.got.compass,locked:!S.flags.gapDone},
        {t:S.race?`Бежать к Шлюзу, пока Прямизна не сомкнулась — ${Math.max(0,Math.ceil(S.race.t))} с`:'Уйти через Шлюз',locked:!S.race}],
      mirror:()=>({g:2,R:RFm}),
      onRoom(r){
        if(r===R('cell')&&!S.flags.freed){S.flags.loops=(S.flags.loops||0)+1;const Mabs=mul(LOOP,mul(S.c.G,S.c.M));S.c={M:Mabs,G:I4(),par:0,cross:0};gs(S.c.M);foldRooms(S.c,A.g);S.room=R('bath');
          flash.style.transition='none';flash.style.opacity=0.6;requestAnimationFrame(()=>{flash.style.transition='opacity .5s';flash.style.opacity=0;});say(S.flags.loops===1?'loop1':'loop2');return;}
        if(r===R('cell')&&S.flags.freed)say('edge');
        if(r===R('gal1'))say('mirror');},
      onLensOn(){},
      tick(dt,p){
        if(S.lensOn&&!S.flags.freed&&S.room===R('bath')){S.flags.freed=1;say('freed');ui.obj();}
        if(S.race){S.race.t-=dt;S.straight=Math.min(1,S.straight+dt/20);
          if(S.race.t<55&&!S.flags.s1){S.flags.s1=1;A.seal('gal2','post');say('sealed');}
          if(S.race.t<30&&!S.flags.s2){S.flags.s2=1;A.seal('cell','gal1');say('sealed');}
          if(Math.random()<dt*3)rotLocal(S.c.M,0,1,(Math.random()-0.5)*0.01*S.straight);
          if(S.race.t%1<dt)ui.obj();
          if(S.race.t<=0)failScreen(CH().raceFail);}},
      onPick(id){if(id==='compass'){S.abil.blink=true;S.race={t:RACE};S.straight=0;ui.obj();say('race');
        for(const G of S.guards){if(G.sleep)continue;if(G.kassel){G.state='search';G.goal=A.pos();G.alert=0.6;G.timer=0;}else G.alert=Math.max(G.alert,0.25);}save();}},
      onSolve(pz){if(pz==='gap')say('gapdone');},
      onExit(){scene(CH().exitScene,()=>completeChapter());},
      restore(s2,o){const f=o.flags||{};if(f.s1)A.seal('gal2','post');if(f.s2)A.seal('cell','gal1');},
      abil:{blink:false,lens:true,decoy:false}};},

  ch3:()=>{const L={start:[0.5,0.18,0],minFloor:-1,maxFloor:2,floorNames:{'-1':'Подвал','0':'Этаж 0 · основание','1':'Этаж 1 · жилые залы','2':'Этаж 2','3':'Этаж 3 · балкон Абсолюта'}};
    const A=makeHouse(L);const P=(x,y,f,h)=>A.pointAt(x,y,f,h);
    const it=[{id:'meter',kind:4,pos:P(0.62,0.42,0,0.3),doc:'meter'},
      {id:'resident',kind:8,vr:3,pos:P(0.78,0.72,1,0.32),name:'Жилец Башни',talk:true,keep:true},
      {id:'child',kind:8,vr:10,pos:P(0.3,0.62,1,0.2),name:'Ребёнок',talk:true,keep:true},
      {id:'pseudo',kind:4,pos:P(0.82,0.85,2,0.4),doc:'pseudo'},
      {id:'wachter',kind:2,pos:P(0.7,0.6,1,0.4),lemma:'wachter'},{id:'horocycle',kind:2,pos:P(0.5,0.85,2,0.4),lemma:'horocycle'},
      {id:'minkowski',kind:2,pos:P(1.5,1.5,0,0.35),lemma:'minkowski'},{id:'sh0',kind:7,pos:P(0.3,0.75,1,0.3)},{id:'sh1',kind:7,pos:P(0.8,0.3,2,0.3)},
      {id:'desk_circ',kind:17,pos:P(0.3,0.25,2,0.3),puzzle:'circ',name:'пароль Криволинейных'},{id:'r151',kind:4,pos:P(0.8,0.15,1,0.4),doc:'r151'},
      ...[[1.15,0.25],[1.85,0.3],[1.5,0.92]].map((q,i)=>({id:'v'+(i+1),kind:19,pos:P(q[0],q[1],3,0.3),name:'точка обзора',talk:true,keep:true,cond:S=>!!S.flags.circDone})),
      {id:'oricycla',kind:8,vr:2,pos:P(1.5,0.5,3,0.33),name:'Сестра Орицикла',talk:true,cond:S=>(S.flags.views||0)>=3},
      {id:'node',kind:9,pos:P(1.5,0.5,3,0.6),name:'Верхняя Машина Башни',talk:true,keep:true,rad:0.45,cond:S=>!!S.got.oricycla},
      {id:'exit',kind:5,pos:P(0.5,0.5,0,0.12),cond:S=>!!S.flags.ch3done,exit:S=>!!S.flags.ch3done}];
    const gd=[{name:'Надзиратель Аммоний',vr:7,route:A.route([[0.55,0.45,1],[0.92,0.45,1],[0.92,0.92,1],[0.55,0.92,1]])},
      {name:'Надзиратель Дидим',vr:7,route:A.route([[0.08,0.5,2],[0.9,0.5,2],[0.9,0.12,2]],1.6)},
      {name:'Надзиратель Филон',vr:7,route:A.route([[1.2,0.2,2],[1.8,0.8,2]],2)}];
    const fl=S=>S.room-100;
    return {A,items:it,guards:gd,
      objectives:S=>{const o=[{t:'Измерить зал: мерный прибор на этаже 0',done:!!S.got.meter},
        {t:'Пароль Криволинейных — чертёжный стол на этаже 2',done:!!S.flags.circDone},
        {t:'Балкон Абсолюта: точки обзора ('+(S.flags.views||0)+'/3)',done:(S.flags.views||0)>=3,locked:!S.flags.circDone},
        {t:'Встретить Сестру Орициклу',done:!!S.got.oricycla,locked:(S.flags.views||0)<3}];
        if(S.choice==='evac')o.push({t:'Вывести жильцов: этаж 1 ('+(S.flags.evac||0)+'/2)',done:(S.flags.evac||0)>=2});
        if(S.choice==='node')o.push({t:'Развести контакты верхнего узла Машины',done:!!S.flags.nodeOff});
        if(S.choice)o.push({t:'Спуститься к люку в основании',locked:!S.flags.ch3done});
        return o;},
      onRoom(r){if(fl(S)===1){say('floor1');say('stealth');}if(fl(S)===2)say('floor2');},
      onLensOn(){say('lens');},
      onSolve(pz){if(pz==='circ'){campaign.lemmas.farkas=1;saveCampaign();L.maxFloor=3;say('circdone');showLemma('farkas');}},
      onTalk(id){
        if(id==='resident'||id==='child'){if(S.choice==='evac'&&!S.got[id]){S.got[id]=1;S.flags.evac=(S.flags.evac||0)+1;say([['vera','Уходите вниз, в подполье. Сейчас.']]);
            if(S.flags.evac>=2){S.flags.ch3done=1;say('evacd');}ui.obj();}else say('talk:'+id);return;}
        if(/^v[123]$/.test(id)){if(S.flags[id])return;S.flags[id]=1;S.flags.views=(S.flags.views||0)+1;say(id);ui.obj();
          if(S.flags.views>=3)setTimeout(()=>scene(CH().lines.defect,()=>{campaign.defectSight=1;saveCampaign();toast('Линза видит дефект');ui.obj();}),5200);return;}
        if(id==='oricycla'){scene(CH().scene,()=>{campaign.decoy=1;S.abil.decoy=true;saveCampaign();const C=CH().choice;
          choose('vera',C.q,C.a,k=>{S.choice=C.a[k].id;campaign.ch3choice=S.choice;saveCampaign();
            const K=new Guard({name:'Циркулятор Кассель',kassel:true,route:A.route([[0.2,0.25,1],[0.85,0.8,1]],1.6)},S.guards.length);S.guards.push(K);
            for(const G of S.guards){if(G.sleep)continue;G.alert=Math.max(G.alert,0.25);}
            if(S.choice==='strike'){S.flags.ch3done=1;AU.tone(60,1.2,'sawtooth',0.08);say('strike');}
            say('kassel');ui.obj();save();lock();});});return;}
        if(id==='node'){if(S.choice!=='node'){toast('Машина гудит над балконом');return;}if(S.flags.nodeOff)return;S.flags.nodeOff=1;S.flags.ch3done=1;say('node');ui.obj();}},
      onExit(){const w=S.choice==='strike'?'oricycla':'nikolai';scene([[w,CH().endBy[S.choice]||'']],()=>completeChapter());},
      restore(s2,o){const f=o.flags||{};if(f.circDone)L.maxFloor=3;if(o.choice&&s2.guards.length<o.guards.length)s2.guards.push(new Guard({name:'Циркулятор Кассель',kassel:true,route:A.route([[0.2,0.25,1],[0.85,0.8,1]],1.6)},s2.guards.length));},
      abil:{blink:true,lens:true,decoy:false}};},

  ch4:()=>{const A=makePlane();const P=(r,d,h)=>A.pointAt(r,d,h);
    const TV=mul(rotZ(45*Math.PI/180),boostX(1.6));                          // центр деревни
    const V=(r,d,h)=>atHeight(apply(TV,polar(r,d)),h??0.16),VF=(r,d)=>apply(TV,polar(r,d));
    // дома: каждый следующий круг больше прежнего (длина окружности растёт как sh r)
    const houses=[];[[0,1],[0.32,5],[0.62,10],[0.9,16]].forEach(([r,n],k)=>{for(let i=0;i<n;i++)houses.push({id:'h'+k+'_'+i,kind:20,pos:V(r,i*360/n+k*13,0.045),inert:true});});
    // квадрат Бернхарда: четыре стороны по 1,2 с поворотом направо на 90°
    const N3=[0,0,1,0],S0=VF(0.42,200);let f=S0.slice(),u=dirTo(S0,VF(1.6,200));const posts=[];
    for(let k=0;k<4;k++){const nx=advancePose(f,u,1.2);f=nx.p;u=nx.u;posts.push(f.slice());
      let w=perpAt(f,u,[-u[1],u[0],0,0]);w=tangent([w[0],w[1],0,w[3]],f);const e=md(w,u);w=tangent(w.map((x,i)=>x-e*u[i]),f);if(det4([...u,...w,...N3,...f])>0)w=w.map(x=>-x);u=w;}
    const miss=hyperbolicDistance(S0,posts[3]);
    const EDGE=polar(4.2,300);
    const it=[...houses,
      {id:'bernhard',kind:8,vr:3,pos:atHeight(S0,0.16),name:'Бернхард',talk:true,keep:true,face:V(0,0)},
      {id:'gausscard',kind:4,pos:V(0.2,250,0.25),doc:'gauss'},
      {id:'vill1',kind:8,vr:3,pos:V(0.5,90),name:'Изгнанник',talk:true,keep:true},{id:'vill2',kind:8,vr:10,pos:V(0.55,320),name:'Изгнанница',talk:true,keep:true},
      ...posts.map((q,k)=>({id:'post'+k,kind:15,pos:atHeight(q,0.11),name:'Веха '+(k+1),cond:S=>S.flags.task&&(k===0||S.got['post'+(k-1)])})),
      {id:'poincare',kind:2,pos:P(1.4,100,0.3),lemma:'poincare'},{id:'riemann',kind:2,pos:P(3.0,220,0.3),lemma:'riemann'},{id:'pentagon',kind:2,pos:P(2.6,150,0.3),lemma:'pentagon'},
      {id:'sh0',kind:7,pos:P(1.2,200,0.3)},{id:'sh1',kind:7,pos:P(2.0,0,0.3)},{id:'r099',kind:4,pos:P(2.0,300,0.3),doc:'r099'},
      ...[0,1,2].map(k=>({id:'wisp'+k,kind:21,pos:P(2.5,300+k*15,0.3),inert:true,cond:S=>!!S.flags.hunt})),
      {id:'oricycla',kind:8,vr:2,pos:V(0.3,20),name:'Сестра Орицикла',talk:true,keep:true,cond:S=>!!S.flags.edgeDone},
      {id:'machine',kind:9,pos:V(0.95,120,0.3),name:'Машина Прямизны',talk:true,keep:true,rad:0.42},
      {id:'exit',kind:5,pos:V(1.15,250,0.2),face:V(0,0),cond:S=>!!S.flags.decided,exit:S=>!!S.flags.decided}];
    const gd=[{name:'Циркулятор Агафон',vr:8,route:A.route([[2.5,250],[2.8,300],[2.2,340]])},{name:'Циркулятор Мина',vr:8,route:A.route([[2.3,185],[2.9,215]],2)}];
    // орициклы-существа: точки орицикла ⟨X, ℓ⟩ = −c вокруг точки абсолюта ℓ
    const horo=(th,c,t)=>{const X=[t*t/2,t,0,1+t*t/2],l=[1,0,0,1],Y=X.map((v,i)=>c*v+(1-c*c)/(2*c)*l[i]);return apply(rotZ(th),Y);};
    const WISP=[{th:5.2,c:0.55},{th:5.4,c:0.7},{th:5.0,c:0.85}];
    const spawnK=()=>{const K=new Guard({name:'Циркулятор Кассель',kassel:true,route:A.route([[2.0,60],[2.4,20]],1.5)},S.guards.length);K.state='search';K.goal=A.pos();K.alert=0.5;return K;};
    const foot=()=>footOf(A.pos());
    return {A,items:it,guards:gd,
      objectives:S=>{const n=[0,1,2,3].filter(k=>S.got['post'+k]).length,o=[{t:'Найти деревню изгнанников',done:!!S.flags.village}];
        o.push({t:'Поговорить с Бернхардом',done:!!S.flags.task,locked:!S.flags.village});
        o.push({t:'Пройти квадрат Бернхарда: вехи ('+n+'/4)',done:n===4,locked:!S.flags.task});
        if(S.flags.hunt)o.push({t:'Уйти от Касселя: подняться выше h = 1 и идти к краю равнины',done:!!S.flags.edgeDone});
        if(S.flags.edgeDone)o.push({t:'Сестра Орицикла у Машины',done:!!S.choice});
        if(S.choice==='evac')o.push({t:'Вывести изгнанников ('+(S.flags.evac||0)+'/2)',done:(S.flags.evac||0)>=2});
        if(S.choice==='reconf')o.push({t:'Перенастроить Машину Прямизны',done:!!S.flags.reconfDone});
        if(S.choice)o.push({t:'Ворота к Цитадели',locked:!S.flags.decided});return o;},
      marks:S=>{const m=[{p:atHeight(O,0.16),c:'#ece5d6',r:6}];if(!S.flags.village)m.push({p:V(0,0),c:'#e8b866',r:11});
        for(let k=0;k<4;k++)if(S.flags.task&&!S.got['post'+k]&&(k===0||S.got['post'+(k-1)])){m.push({p:posts[k],c:'#6fd3ff',r:10});break;}
        if(S.flags.task)m.push({p:S0,c:'#ffffff',r:5});if(S.flags.hunt&&!S.flags.edgeDone)m.push({p:EDGE,c:'#ff8a6a',r:10});
        if(S.flags.decided)m.push({p:V(1.15,250),c:'#ffffff',r:11});return m;},
      start(){},
      tick(dt,p){const fp=foot();
        if(!S.flags.village&&hyperbolicDistance(fp,VF(0,0))<0.7){S.flags.village=1;say('village');ui.obj();}
        if(S.flags.hunt){WISP.forEach((w,k)=>{const t=Math.sin(S.time*0.15+k*2)*2.2;const q=horo(w.th,w.c,t);const it2=S.items.find(i=>i.id==='wisp'+k);it2.pos=atHeight(q,0.3);
            if(hyperbolicDistance(fp,q)<0.22&&!S.flags['wt'+k]){S.flags['wt'+k]=1;say('wisp');const t2=t+0.8*Math.sign(Math.cos(S.time*0.15+k*2)||1),q2=horo(w.th,w.c,t2);
              const c=S.c,fwd=dirTo(fp,q2),dd=hyperbolicDistance(fp,q2);const dl=apply(linv(mul(c.G,c.T)),fwd),phi=Math.atan2(dl[1],dl[0]);
              c.T=mul(c.T,mul(mul(rotZ(phi),boostX(dd/Math.cosh(c.h))),rotZ(-phi)));c.T=gsPlane(c.T);foldPlane(c);}});
          if(S.lensOn){const K=S.guards.find(g=>g.kassel);if(K&&Math.random()<dt*0.8){K.goal=A.pos();if(K.state==='patrol'||K.state==='return')K.state='search';}}
          if(!S.flags.edgeDone&&S.c.h>=1&&hyperbolicDistance(fp,O)>3.7){S.flags.edgeDone=1;
            scene(CH().lines.edge,()=>{const c=S.c;c.T=I4();c.G=I4();c.h=0.45;const d=apply(TV,polar(0.7,60));const r=Math.acosh(d[3]),ang=Math.atan2(d[1],d[0]);
              c.T=mul(rotZ(ang),boostX(r));c.T=gsPlane(c.T);foldPlane(c);for(const G of S.guards){G.alert=0;G.state='return';G.scan=null;}ui.obj();save();});}}},
      onPick(id){if(id==='post3'){say('square');toast('Квадрат не замкнулся: до начала '+fmt(miss)+' (на евклидовой плоскости — 0)');ui.obj();}else if(id.startsWith('post'))say('post');},
      onTalk(id){
        if(id==='bernhard'){if(!S.flags.task){S.flags.task=1;scene(CH().lines.master,()=>{showPlaque(CH().note);ui.obj();});return;}
          if(S.got.post3&&!S.flags.hunt){S.flags.hunt=1;scene(CH().lines.master2,()=>{S.guards.push(spawnK());say('hunt');ui.obj();save();});return;}
          toast(S.flags.hunt?'Бернхард: «Уходи. Он рядом».':'Бернхард: «Вехи ждут»');return;}
        if(id==='vill1'||id==='vill2'){if(S.choice==='evac'&&!S.got[id]){S.got[id]=1;S.flags.evac=(S.flags.evac||0)+1;say(CH().lines['talk:evac']);if(S.flags.evac>=2)decide();ui.obj();}else say('talk:'+id);return;}
        if(id==='oricycla'){if(S.choice)return;scene(CH().lines.oricycla,()=>{const C=CH().choice;choose('vera',C.q,C.a,k=>{S.choice=C.a[k].id;campaign.ch4choice=S.choice;saveCampaign();
            if(S.choice==='strike'){AU.tone(55,1.4,'sawtooth',0.09);campaign.ch4cost=1;saveCampaign();toast('Машина замолкает. Часть домов рушится.');decide();}ui.obj();save();lock();});});return;}
        if(id==='machine'){if(S.choice!=='reconf'||S.flags.reconfDone){toast('Машина Прямизны гудит чистым тоном');return;}const Q=CH().reconfQ;
          choose('vera',Q.q,Q.a,k=>{if(Q.a[k].ok){S.flags.reconfDone=1;say('reconf');decide();}else toast('Машина дрогнула и не приняла настройку. Проверьте: дефект = 3π − сумма углов.');ui.obj();lock();});}},
      onExit(){scene(CH().lines.decide,()=>completeChapter());},
      restore(s2,o){if(o.flags&&o.flags.hunt&&s2.guards.length<o.guards.length)s2.guards.push(new Guard({name:'Циркулятор Кассель',kassel:true,route:A.route([[2.0,60],[2.4,20]],1.5)},s2.guards.length));},
      abil:{blink:true,lens:true,decoy:true}};
    function decide(){S.flags.decided=1;ui.obj();}},

  ch5:()=>{const L={poly:[4,5],pal:2,lamp:[1.0,0.86,0.66],fog:7,
      rooms:[['gate',null,null,'Врата трёх геометрий',0],['nave','gate',[0,0,1],'Неф',1],['hall','nave',[1,0,0.3],'Зал украденных углов',1],['scri','hall',[1,0,-0.2],'Реестр',1],
        ['cloi','nave',[-1,0,0.3],'Клуатр',0],['crypt','cloi',[-0.5,-1,0.2],'Крипта',0],['loggia','hall',[0.5,1,0.3],'Лоджия',0],
        ['stair','nave',[0,1,0.6],'Лестница',0],['choir','stair',[0,1,0.3],'Хоры',1],['sanct','choir',[0.3,1,0],'Собор Прямых Углов',1],['heart','sanct',[0,1,0.4],'Сердце Машин',1]],
      seal:[['gate','nave'],['sanct','heart']],start:{room:'gate',toward:'nave'}};
    const A=makeRooms(L);const P=(r,o)=>A.pointIn(r,o),C=id=>A.ROOMS[A.RI(id)].c;
    const sc=C('sanct'),gt=C('gate'),hc=C('heart'),hl=C('hall');
    const gateSanct=A.ROOMS[A.RI('gate')].nb.includes(A.RI('sanct'))||Math.abs(hyperbolicDistance(gt,sc)-hyperbolicDistance(gt,C('nave')))<0.01;
    if(gateSanct)L.seal.push(['gate','sanct']);A.seal&&gateSanct&&A.seal('gate','sanct');
    const mach=advancePose(hc,dirTo(hc,sc),-0.3).p,machH=advancePose(hl,dirTo(hl,C('nave')),-0.3).p;
    const hp=perpAt(machH,dirTo(machH,hl)),hq=perpAt(machH,dirTo(machH,hl),hp);
    const node=(k)=>{const d=dirTo(hc,sc),w=perpAt(hc,d);return advancePose(hc,tangent(d.map((x,i)=>Math.cos(k)*x+Math.sin(k)*w[i]),hc),0.3).p;};
    const it=[
      {id:'door_h',kind:16,pos:A.faceCenter('gate','nave'),face:gt,talk:true,keep:true,name:'Гиперболическая дверь',rad:0.5,cond:S=>!S.flags.gateOpen},
      {id:'door_e',kind:16,pos:P('gate',[0.47,0,0]),face:gt,talk:true,keep:true,name:'Евклидова дверь',rad:0.5,cond:S=>!S.lensOn&&!S.flags.gateOpen},
      {id:'door_s',kind:16,pos:P('gate',[-0.47,0,0]),face:gt,talk:true,keep:true,name:'Сферическая дверь',rad:0.5,cond:S=>!S.lensOn&&!S.flags.gateOpen},
      ...(gateSanct?[{id:'grille',kind:16,pos:A.faceCenter('gate','sanct'),face:sc,inert:true}]:[]),
      {id:'machH',kind:9,pos:machH,name:'Печь углов',inert:true,rad:0.42},
      ...[0,1,2,3,4,5].map(k=>({id:'fall'+k,kind:7,pos:machH,inert:true})),
      {id:'worker',kind:8,vr:8,pos:P('hall',[0.15,-0.25,-0.1]),face:machH,name:'Истопник',talk:true,keep:true},
      {id:'registry',kind:4,pos:P('scri',[0.1,-0.2,0.1]),doc:'registry',name:'Главный реестр'},
      {id:'beltrami',kind:2,pos:P('crypt',[0.2,0.25,-0.1]),lemma:'beltrami'},{id:'klein',kind:2,pos:P('loggia',[-0.2,0.22,0.12]),lemma:'klein'},
      {id:'sh0',kind:7,pos:P('cloi',[0.22,-0.2,0.1])},{id:'sh1',kind:7,pos:P('stair',[-0.2,0.2,-0.15])},{id:'sh2',kind:7,pos:P('loggia',[0.2,-0.2,0.1])},{id:'r001',kind:4,pos:P('crypt',[-0.2,-0.2,0.15]),doc:'r001'},
      {id:'euclid',kind:8,vr:5,pos:advancePose(sc,dirTo(sc,hc),0.25).p,face:C('choir'),name:'Архипрелат Евклид',talk:true,keep:true,cond:S=>!S.flags.nodes},
      {id:'machine',kind:9,pos:mach,name:'Сердце Машин',inert:true,rad:0.42},
      {id:'nodeS',kind:17,puzzle:'straightSq',pos:node(-1.1),name:'Узел Прямизны',cond:S=>!!S.flags.nodes&&!S.escape},
      {id:'nodeC',kind:17,puzzle:'breakEdge',pos:node(1.1),name:'Узел Кривизны',cond:S=>!!S.flags.nodes&&!S.escape},
      {id:'nodeP',kind:17,puzzle:'compat',pos:advancePose(hc,dirTo(hc,sc),0.2).p,name:'Пустой стол',cond:S=>!!S.flags.nodes&&!S.escape,req:S=>!!S.flags.secret,reqLine:'emptyTable'},
      {id:'flight',kind:5,pos:advancePose(gt,dirTo(gt,C('nave')),-0.35).p,face:C('nave'),cond:S=>!!S.escape,fin:true}];
    const gd=[{name:'Страж Нефа Варсонофий',vr:9,route:A.route(['nave','cloi','crypt','cloi'])},{name:'Страж Зала Поликарп',vr:9,route:A.route(['hall','scri','hall','loggia'],2)},
      {name:'Страж Собора Евлогий',vr:9,route:A.route(['choir','sanct'],2.4)},{name:'Циркулятор Кассель',route:A.route(['stair','choir'],2.2),kassel:true}];
    const K=()=>S.guards.find(g=>g.kassel);
    const mercy=()=>!(campaign.kchase>0)&&!(S.stats.kchase>0);
    return {A,items:it,guards:gd,
      objectives:S=>{if(S.escape)return [{t:'Бежать из Цитадели — к Вратам, в обход ребра'+(S.escape.id==='postulate'?(K()&&!K().passive?' (охотится только Кассель)':' (никто не преследует)'):'')}];
        const o=[{t:'Пройти Врата трёх геометрий',done:!!S.flags.gateOpen}];
        o.push({t:'Найти зал украденных углов',done:!!S.flags.hall,locked:!S.flags.gateOpen});
        o.push({t:'Главный реестр вычеркнутых',done:!!S.got.registry,locked:!S.flags.gateOpen});
        o.push({t:'Подняться в Собор Прямых Углов',done:!!S.flags.sanct,locked:!S.flags.gateOpen});
        if(S.flags.sanct)o.push({t:'Говорить с Архипрелатом Евклидом',done:!!S.flags.nodes});
        if(S.flags.nodes)o.push({t:'Сердце Машин: выбрать узел и начертить',done:!!S.escape});return o;},
      marks:S=>{const m=[];if(!S.flags.gateOpen)m.push({p:A.faceCenter('gate','nave'),c:'#e8b866',r:10});
        else if(!S.flags.nodes)m.push({p:sc,c:'#e8b866',r:10});else if(!S.escape)m.push({p:hc,c:'#6fd3ff',r:10});else m.push({p:gt,c:'#ffffff',r:11});return m;},
      start(){say('start');setTimeout(()=>!S.flags.gateOpen&&say('gates'),5200);},
      tick(dt){const t=S.time;for(let k=0;k<6;k++){const it2=S.items.find(i=>i.id==='fall'+k);if(!it2)continue;const ph=(t*0.35+k/6)%1,a=k*1.05+t*0.2;
          const w=tangent(hp.map((x,i)=>Math.cos(a)*x+Math.sin(a)*hq[i]),machH);it2.pos=advancePose(advancePose(machH,dirTo(machH,hl),0.1+0.25*(1-ph)).p,w,0.12).p;}},
      onRoom(r){const R=id=>r===A.RI(id);
        if(R('hall')&&!S.flags.hall){S.flags.hall=1;say('hall');ui.obj();}
        if(R('stair')&&!S.flags.kmet){S.flags.kmet=1;const G=K();if(!G)return;
          if(mercy()){G.passive=true;G.state='return';G.alert=0;scene(CH().kasselMercy,()=>{const Q=CH().kasselMercyChoice;choose('vera',Q.q,Q.a,k=>{
              if(Q.a[k].id==='give'){S.flags.kgive=1;campaign.kasselSpared=1;saveCampaign();G.route=A.route(['stair'],99);scene(CH().kasselSpared,()=>{ui.obj();save();lock();});}
              else{toast('Кассель смотрит вслед. Маятник неподвижен.');ui.obj();save();lock();}});});}
          else{G.state='search';G.goal=A.pos();G.alert=0.5;G.timer=0;say('kasselHunt');}}
        if(R('choir'))say('near');
        if(R('sanct')&&!S.flags.sanct){S.flags.sanct=1;ui.obj();}
        if(R('heart')&&!S.flags.ori){S.flags.ori=1;say(campaign.ch3choice==='strike'||campaign.ch4choice==='strike'?'oriLink:strike':'oriLink:other');}},
      onPick(id){if(id==='registry'){if(Object.keys(campaign.records||{}).length>=4)setTimeout(()=>say('chorus'),6500);ui.obj();}},
      onTalk(id){
        if(id==='door_h'){if(!S.lensOn){toast('Три двери — одинаковы. Посмотрите сквозь Линзу (V)');return;}
          S.flags.gateOpen=1;A.unseal('gate','nave');AU.tone(70,0.8,'sawtooth',0.06);toast('Гиперболическая дверь: пять кубов у ребра, 5 × 72° = 360°');ui.obj();save();return;}
        if(id==='door_e'||id==='door_s'){say(id==='door_e'?'door:euclid':'door:sphere');return;}
        if(id==='worker'){say('talk:worker');return;}
        if(id==='euclid'&&!S.flags.nodes)debate();},
      onSolve(pz){const id={straightSq:'straight',breakEdge:'curved',compat:'postulate'}[pz];if(id)startEscape(id,S.flags.score||0);},
      restore(s2,o){const f=o.flags||{};if(f.gateOpen)A.unseal('gate','nave');if(f.nodes)A.unseal('sanct','heart');},
      abil:{blink:true,lens:true,decoy:true}};},
};

// ═══════════════ стражи ═══════════════
const FOV=80*Math.PI/180,VIEW=4.5,RATE=3.0,CATCH=0.30;
class Guard{
  constructor(sp,idx){this.idx=idx;this.name=sp.name;this.kassel=!!sp.kassel;this.vr=sp.vr||0;this.route=sp.route;this.wp=1%sp.route.length;
    this.pos=sp.route[0].p.slice();this.dir=dirTo(this.pos,sp.route[this.wp].p);if(!(md(this.dir,this.dir)>0.5))this.dir=perpAt(this.pos,[1,0,0,0]);
    this.state='patrol';this.alert=0;this.sleep=false;this.timer=0;this.wait=0;this.goal=null;this.lastSeen=null;
    this.seenAgo=99;this.found=false;this.scan=null;this.sees=0;this.barkT=0;
    this.fov=this.kassel?95*Math.PI/180:FOV;this.view=this.kassel?5.5:VIEW;}
  turn(des,dt,rate){const k=1-Math.exp(-(rate??3.2)*dt);this.dir=tangent(this.dir.map((x,i)=>x*(1-k)+des[i]*k),this.pos);}
  moveTo(tg,sp,dt){const d=hyperbolicDistance(this.pos,tg);if(d<0.05)return true;const des=dirTo(this.pos,tg);this.turn(des,dt);
    if(md(this.dir,des)<Math.cos(0.5))return false;const s=Math.min(d,sp*(this.kassel?1.15:1)*dt);const nx=advancePose(this.pos,this.dir,s);
    this.mvT=S.time;this.pos=nx.p;this.dir=nx.u;if(S.A.constrain){this.pos=S.A.constrain(this.pos);this.dir=tangent(this.dir,this.pos);}return d-s<0.05;}
  look(dt){if(!this.scan){this.scan={d0:this.dir.slice(),pp:perpAt(this.pos,this.dir,S.A.kind==='plane'?null:null),t:0};}
    const s=this.scan;s.t+=dt;const ph=1.0*Math.sin(s.t*1.5);
    let pp=s.pp;if(S.A.kind==='plane'){const up=tangent([0,0,1,0],this.pos);pp=perpAt(this.pos,up,s.d0);void pp;
      // на равнине осматриваемся по горизонтали
      const n=up,dd=s.d0;pp=tangent([dd[1]*n[2]-dd[2]*n[1],dd[2]*n[0]-dd[0]*n[2],dd[0]*n[1]-dd[1]*n[0],0],this.pos);}
    this.turn(tangent(s.d0.map((x,i)=>Math.cos(ph)*x+Math.sin(ph)*pp[i]),this.pos),dt,4);}
  perceive(px,lightF,motionF){const d=hyperbolicDistance(this.pos,px);if(d>this.view)return 0;
    const ang=Math.acos(clamp(md(this.dir,dirTo(this.pos,px)),-1,1)),half=this.fov/2;
    let base=ang<=half?0.55+0.45*(1-ang/half):(d<0.45?0.55:0);if(!base)return 0;
    if(!S.A.los(this.pos,px))return 0;const sh=Math.sinh(d);
    // в Башне стражи смотрят вдоль своего этажа: сквозь стеклянный пол видят плохо
    const fl=S.A.kind==='house'&&S.A.roomOf(this.pos)!==S.A.roomOf(px)?0.18:1;
    return base*lightF*motionF*fl/(1+0.9*sh*sh);}
  sees_(x,maxD){const d=hyperbolicDistance(this.pos,x);if(d>maxD)return false;
    if(Math.acos(clamp(md(this.dir,dirTo(this.pos,x)),-1,1))>this.fov/2)return false;return S.A.los(this.pos,x);}
  toJSON(){const o={};for(const k of ['wp','pos','dir','state','alert','sleep','timer','wait','goal','lastSeen','seenAgo','found','passive'])o[k]=this[k];return o;}
}

// ═══════════════ интерфейс ═══════════════
const css=`
#mhud{position:fixed;inset:0;pointer-events:none;display:none;font-family:var(--body)}
#mhud.on{display:block}
#mhud>*{pointer-events:none}
#mobj{position:absolute;left:calc(16px + env(safe-area-inset-left,0px));top:calc(14px + env(safe-area-inset-top,0px));max-width:min(440px,calc(100vw - 32px));text-shadow:0 1px 8px #000}
#mobj .ch{font-size:11px;letter-spacing:.14em;text-transform:uppercase;color:var(--brass)}
#mobj .rn{font-family:var(--display);font-size:28px;line-height:1.05;margin:2px 0 8px;min-height:4px}
#mobj ul{list-style:none;margin:0;padding:0;display:flex;flex-direction:column;gap:3px;font-size:13px}
#mobj li::before{content:"◇ ";color:var(--brass)}
#mobj li.done{color:var(--muted);text-decoration:line-through}
#mobj li.done::before{content:"◆ "}
#mobj li.locked{color:var(--muted);opacity:.6}
#mbar{position:absolute;left:calc(16px + env(safe-area-inset-left,0px));bottom:calc(16px + env(safe-area-inset-bottom,0px));display:flex;flex-direction:column;gap:6px;background:var(--panel);padding:4px 6px;min-width:240px}
#mbar .lbl{display:flex;justify-content:space-between;font-size:11px;letter-spacing:.1em;text-transform:uppercase;color:var(--muted)}
#mbar .track{height:6px;background:rgba(255,255,255,.08);border-radius:3px;overflow:hidden}
#mbar .fill{height:100%;background:linear-gradient(90deg,#4b36a8,#8f74ff 70%,#d9ccff);width:50%;box-shadow:0 0 10px #8f74ff}
#mbar .ab{display:flex;gap:10px;font-size:12px;color:var(--fg);flex-wrap:wrap}
#mbar .ab span.off{opacity:.3}
#mbar kbd{font:500 10px var(--mono);border:1px solid var(--line);border-radius:2px;padding:1px 4px;margin-right:4px;color:var(--brass)}
#mprompt{position:absolute;left:50%;top:calc(50% + 34px);transform:translateX(-50%);font-size:14px;color:var(--fg);background:rgba(12,14,28,.7);border:1px solid var(--line);border-radius:3px;padding:6px 12px;display:none;white-space:nowrap}
#mprompt b{color:var(--brass);font-family:var(--mono);font-weight:500}
#msub{position:absolute;left:50%;transform:translateX(-50%);bottom:calc(96px + env(safe-area-inset-bottom,0px));width:min(760px,calc(100vw - 32px));display:flex;gap:14px;align-items:center;justify-content:center;transition:opacity .5s;opacity:0}
#msub .portrait{width:58px;height:70px;flex:none;filter:drop-shadow(0 2px 8px #000)}
#msub .tx{font-family:var(--serif);font-style:italic;font-size:18px;line-height:1.45;color:var(--fg);text-shadow:0 1px 6px #000,0 0 18px #000;text-align:left}
#msub .who{color:var(--brass);font:600 11px var(--body);font-style:normal;letter-spacing:.16em;text-transform:uppercase;display:block;margin-bottom:2px}
#mbark{position:absolute;left:50%;top:calc(50% - 90px);transform:translateX(-50%);font-family:var(--serif);font-style:italic;font-size:16px;color:#f0e3c4;text-shadow:0 1px 6px #000,0 0 12px #000;opacity:0;transition:opacity .4s;white-space:nowrap}
#mbark b{font:600 10px var(--body);font-style:normal;letter-spacing:.14em;text-transform:uppercase;color:var(--brass);margin-right:8px}
#mtitle{position:absolute;left:50%;top:22%;transform:translateX(-50%);font-family:var(--display);font-size:52px;letter-spacing:.01em;color:var(--fg);text-shadow:0 2px 20px #000;opacity:0;transition:opacity .8s;text-align:center;white-space:nowrap}
#mtitle small{display:block;font-family:var(--body);font-size:11px;letter-spacing:.3em;text-transform:uppercase;color:var(--brass);margin-bottom:4px}
#mtitle i{display:block;margin:8px auto 0;width:220px;height:9px;background:linear-gradient(90deg,transparent,var(--brass) 30%,transparent 48%,transparent 52%,var(--brass) 70%,transparent) center/100% 1px no-repeat,radial-gradient(circle,var(--brass) 0 3px,transparent 3.5px) center/9px 9px no-repeat}
#mplaque{pointer-events:auto!important;position:absolute;right:calc(16px + env(safe-area-inset-right,0px));top:calc(14px + env(safe-area-inset-top,0px));width:min(420px,calc(100vw - 32px));background:radial-gradient(ellipse at top,#1b2038,#0d1020);padding:8px 10px;display:none;line-height:1.55}
#mplaque .hd{display:flex;gap:12px;align-items:center;margin-bottom:6px}
#mplaque .portrait{width:64px;height:77px;flex:none}
#mplaque h4{margin:0;font-family:var(--display);font-size:26px;color:var(--brass);font-weight:400;line-height:1.05}
#mplaque .by{font-size:11px;letter-spacing:.08em;color:var(--muted);margin-top:3px}
#mplaque p{margin:0;font-family:var(--serif);font-size:15px}
#mplaque .k{margin-top:8px;font-size:11px;color:var(--muted)}
#mind .gi{position:absolute;transform:translate(-50%,-100%);width:22px;height:13px;border-radius:50%;border:2px solid #f2c063;overflow:hidden;box-shadow:0 0 6px #000}
#mind .gi i{position:absolute;left:0;bottom:0;width:100%;background:#f2c063}
#mind .gi.chase{border-color:#ff3b26}#mind .gi.chase i{background:#ff3b26}
#mind .gi.k{border-color:#ff6b4a;width:26px}
#mflash{position:fixed;inset:0;pointer-events:none;background:radial-gradient(circle,rgba(160,220,255,0) 20%,rgba(160,220,255,.55));opacity:0;transition:opacity .35s}
#mlensv{position:fixed;inset:0;pointer-events:none;background:radial-gradient(ellipse at center,rgba(60,120,255,0) 45%,rgba(40,90,220,.35));opacity:0;transition:opacity .25s}
#mscreen{position:fixed;inset:0;display:none;align-items:center;justify-content:center;padding:16px;background:rgba(6,8,16,.84);backdrop-filter:blur(6px);-webkit-backdrop-filter:blur(6px);pointer-events:auto;z-index:5}
#mscreen.on{display:flex}
#mscreen .card{width:min(680px,100%);max-height:calc(100vh - 32px);overflow:auto;background:radial-gradient(ellipse at top,#1c2140,#0c0f1c 70%);padding:16px 22px;line-height:1.55;box-shadow:0 20px 80px rgba(0,0,0,.6)}
#mscreen .crest{display:flex;flex-direction:column;align-items:center;text-align:center;margin:4px 0 14px}
#mscreen .crest svg{width:96px;height:96px;filter:drop-shadow(0 0 14px rgba(214,163,90,.35))}
#mscreen .wordmark{margin-top:12px;line-height:0;max-width:100%}#mscreen .wordmark svg{max-width:100%}
#mscreen .fxl{display:block;margin:2px auto 0;line-height:0}
#mscreen .ch{font-size:11px;letter-spacing:.16em;text-transform:uppercase;color:var(--brass)}
#mscreen .crest .ch{margin-top:8px}
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
#mscreen .btn:disabled{opacity:.35;cursor:default}
#mscreen .quiz{border:1px solid var(--line);padding:10px 12px;margin:12px 0}#mscreen .chk{display:flex;flex-direction:column;align-items:flex-start;gap:4px}#mscreen .chk .btn{text-transform:none;letter-spacing:0;font-size:13px;text-align:left}
#mscreen .gl{margin:8px 0}#mscreen .gl b{font-family:var(--display);font-size:19px;font-weight:400;color:var(--brass)}#mscreen .gl small{color:var(--muted);margin-left:6px}
#mscreen .card2{border:1px solid var(--line);padding:10px 12px;margin:10px 0;font-size:14px}#mscreen .card2 h4{margin:0 0 6px;font-family:var(--display);font-weight:400;font-size:22px}
#mscreen details{margin-top:6px;font-size:13px}#mscreen summary{cursor:pointer;color:var(--brass)}
#mscreen .chlist{display:flex;flex-direction:column;gap:6px;margin:10px 0}
#mscreen .chlist button{all:unset;cursor:pointer;display:flex;justify-content:space-between;gap:12px;padding:9px 12px;border:1px solid var(--line);font-family:var(--serif);font-size:16px}
#mscreen .chlist button:hover{border-color:var(--brass)}
#mscreen .chlist button small{font:500 11px var(--body);letter-spacing:.1em;text-transform:uppercase;color:var(--brass)}
#mscreen .chlist button:disabled{opacity:.35;cursor:default}
#mscreen .gallery{display:grid;grid-template-columns:repeat(auto-fill,minmax(130px,1fr));gap:14px;margin:12px 0}
#mscreen .gallery figure{margin:0;text-align:center;font-size:12px;line-height:1.3}
#mscreen .gallery svg{width:100%;height:auto}
#mscreen .gallery figcaption b{display:block;font-family:var(--serif);font-size:14px;font-weight:400;color:var(--fg)}
#mscreen .gallery figcaption span{color:var(--muted)}
#mscreen .gallery figure.lock svg{filter:grayscale(1) brightness(.35)}
#mscreen .lem{display:flex;gap:12px;margin:10px 0;align-items:flex-start}
#mscreen .lem .portrait{width:60px;height:72px;flex:none}
#mscreen .lem p{font-size:14.5px;margin:2px 0 0}
#mscreen .lem b{font-family:var(--display);font-size:20px;font-weight:400;color:var(--brass)}
#mdlg{position:fixed;left:50%;bottom:calc(24px + env(safe-area-inset-bottom,0px));transform:translateX(-50%);width:min(820px,calc(100vw - 24px));display:none;z-index:6;pointer-events:auto;background:radial-gradient(ellipse at top,#1c2140,#0b0e1a 75%);padding:12px 16px;box-shadow:0 20px 80px rgba(0,0,0,.7)}
#mdlg.on{display:flex;gap:18px;align-items:flex-start}
#mdlg .portrait{width:120px;height:144px;flex:none}
#mdlg .bd{flex:1;min-width:0}
#mdlg .nm{font:600 11px var(--body);letter-spacing:.16em;text-transform:uppercase;color:var(--brass)}
#mdlg .sb{font-size:11px;color:var(--muted);margin-bottom:6px}
#mdlg .tx{font-family:var(--serif);font-size:18px;line-height:1.5;min-height:3em}
#mdlg .tx.narr{font-style:italic;color:#d9cfb8}
#mdlg .opts{display:flex;flex-direction:column;gap:6px;margin-top:10px}
#mdlg .opts button{all:unset;cursor:pointer;padding:8px 12px;border:1px solid var(--line);font-family:var(--serif);font-size:15.5px;line-height:1.4}
#mdlg .opts button:hover,#mdlg .opts button:focus-visible{border-color:var(--brass);background:rgba(214,163,90,.08)}
#mdlg .opts button small{display:block;font:12px var(--body);color:var(--muted);margin-top:2px}
#mdlg .nx{margin-top:8px;font-size:11px;color:var(--muted);letter-spacing:.08em}
#mtouch{position:absolute;right:calc(20px + env(safe-area-inset-right,0px));bottom:calc(150px + env(safe-area-inset-bottom,0px));display:none;flex-direction:column;gap:10px;pointer-events:auto}
#mtouch button{width:56px;height:56px;border-radius:50%;border:1px solid var(--line);background:rgba(12,14,28,.65);color:var(--fg);font-size:11px;touch-action:none}
#mpause{position:absolute;right:calc(16px + env(safe-area-inset-right,0px));top:calc(14px + env(safe-area-inset-top,0px));pointer-events:auto;display:none}
#mlect{position:absolute;right:calc(16px + env(safe-area-inset-right,0px));bottom:calc(16px + env(safe-area-inset-bottom,0px));width:min(300px,calc(100vw - 32px));background:var(--panel);padding:4px 8px;display:none;font-size:12.5px;line-height:1.5}
#mlect h5{margin:0 0 4px;font:600 10.5px var(--body);letter-spacing:.14em;text-transform:uppercase;color:var(--brass)}
#mlect .th{font-family:var(--serif);font-size:13.5px;margin-bottom:6px}
#mlect .rw{display:flex;justify-content:space-between;gap:10px;font-family:var(--mono);font-size:12px}
#mtoast{position:absolute;left:50%;top:calc(14px + env(safe-area-inset-top,0px));transform:translateX(-50%);font-size:13px;background:var(--panel);border:1px solid var(--line);border-radius:3px;padding:6px 12px;opacity:0;transition:opacity .4s}
#mmap{position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);width:min(520px,calc(100vw - 32px));aspect-ratio:1;background:rgba(8,12,26,.92);border:1px solid var(--brass);border-radius:50%;display:none;pointer-events:none;z-index:4}
#mmap.on{display:block}
@media print{body>*:not(#mscreen){display:none!important}#mscreen{position:static;background:#fff;backdrop-filter:none}#mscreen .card{background:#fff;color:#000;max-height:none;box-shadow:none;border:0}#mscreen .row,#mscreen .btn{display:none}}
#mtbl{position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);width:min(980px,calc(100vw - 24px));max-height:calc(100vh - 24px);overflow:auto;display:none;z-index:7;background:radial-gradient(ellipse at top,#1c2140,#0b0e1a 75%);padding:12px 16px;pointer-events:auto;box-shadow:0 20px 80px rgba(0,0,0,.7)}
#mtbl.on{display:flex;gap:18px;flex-wrap:wrap;align-items:flex-start;animation:p5fade .35s ease both}
#mtbl canvas{width:min(520px,100%);aspect-ratio:1;border:1px solid var(--line);touch-action:none;cursor:crosshair}
#mtbl .side{flex:1;min-width:240px;line-height:1.5}#mtbl .side p{font-family:var(--serif);font-size:15px;margin:0 0 10px}
#mtbl h4{margin:2px 0 8px;font-family:var(--display);font-weight:400;font-size:30px}#mtbl .ch{font-size:11px;letter-spacing:.16em;text-transform:uppercase;color:var(--brass)}
#mtbl .tasks{padding-left:0;list-style:none;font-size:14px}#mtbl .tasks li::before{content:"◇ ";color:var(--brass)}#mtbl .tasks li.done{color:#9fdc8a}#mtbl .tasks li.done::before{content:"◆ "}
#mtbl .btn{margin:0 6px 6px 0}
#mtbl .dials .row{margin:0 0 4px;display:flex;align-items:center;gap:4px;flex-wrap:wrap}#mtbl .dials .mono{width:62px;color:var(--muted);font-size:12px}#mtbl .dials .btn{padding:5px 9px;margin:0}
#mintro{position:fixed;inset:0;z-index:9;background:#000;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:24px;transition:opacity .6s;cursor:pointer}
#mintro.out{opacity:0}#mintro svg{width:min(260px,50vw);transition:opacity 1s}#mintro svg.gone{opacity:0}
#mintro path{stroke-dasharray:420;stroke-dashoffset:420;animation:p5draw 3s ease forwards}
#mintro .cap{font-family:var(--serif);font-style:italic;font-size:clamp(18px,3vw,28px);color:#ece5d6;opacity:0;transition:opacity .6s;text-align:center;padding:0 16px}#mintro .cap.on{opacity:1}
#mintro .skip{position:absolute;bottom:20px;font:11px var(--body);letter-spacing:.14em;text-transform:uppercase;color:#6c6658}
@keyframes p5draw{to{stroke-dashoffset:0}}
@keyframes p5in{from{opacity:0;transform:translateY(10px) scale(.985)}to{opacity:1;transform:none}}
@keyframes p5fade{from{opacity:0}to{opacity:1}}
@keyframes p5pulse{0%,100%{transform:translate(-50%,-100%) scale(1)}50%{transform:translate(-50%,-100%) scale(1.25)}}
#mtitle .fx path,#mscreen .wordmark .fx path,#mscreen .fxl .fx path{stroke-dasharray:64;stroke-dashoffset:64;animation:p5draw 1.6s cubic-bezier(.4,.1,.2,1) forwards}
#mscreen.on .card{animation:p5in .45s ease both}
#mdlg.on{animation:p5fade .35s ease both}#mdlg.on .tx{animation:p5fade .5s ease both}
#msub .portrait{animation:p5fade .6s ease both}
#mind .gi.chase{animation:p5pulse .5s ease-in-out infinite}
@media (prefers-reduced-motion:reduce){#mtitle .fx path,#mscreen .fx path{animation:none;stroke-dashoffset:0}#mscreen.on .card,#mdlg.on{animation:none}}
@media (pointer:coarse){#mtouch{display:flex}#mpause{display:block}}
#mtouch button.on{border-color:var(--brass);background:rgba(214,163,90,.28)}
#mtouch button.act{background:rgba(214,163,90,.22);border-color:var(--brass);font-weight:600;font-size:15px}
#mt-crouch{display:none}
#mrot{position:fixed;inset:0;z-index:12;background:rgba(5,7,14,.94);display:none;flex-direction:column;align-items:center;justify-content:center;gap:14px;text-align:center;padding:24px;pointer-events:auto;font-family:var(--serif)}
#mrot div{font-size:64px;color:var(--brass);animation:p5rot 2.4s ease-in-out infinite}#mrot p{font-size:18px;max-width:300px;margin:0}
@keyframes p5rot{0%,30%{transform:rotate(0)}60%,100%{transform:rotate(-90deg)}}
@media (pointer:coarse){
  #mbar .ab{display:none}
  #mprompt{pointer-events:auto!important;cursor:pointer;font-size:15px;padding:10px 16px}
  #mtouch{display:grid!important;grid-template-columns:repeat(2,56px);gap:8px;bottom:calc(150px + env(safe-area-inset-bottom,0px))}
  #mtouch button{width:56px;height:56px}
  #mpause{min-width:44px;min-height:44px}
  #mdlg .opts button{padding:12px 14px}
  #mscreen .btn{padding:12px 16px}
}
@media (pointer:coarse) and (orientation:portrait){body.p5play:not(.p5rotok) #mrot{display:flex}}
@media (pointer:coarse) and (max-height:520px){
  #mobj{max-width:40vw;top:calc(8px + env(safe-area-inset-top,0px))}#mobj .ch{font-size:9px}#mobj .rn{font-size:16px;margin:0 0 4px}#mobj ul{font-size:11px;gap:1px}
  #mobj li.done{display:none}
  #mbar{left:auto;right:calc(76px + env(safe-area-inset-right,0px));top:calc(10px + env(safe-area-inset-top,0px));bottom:auto!important;min-width:150px;gap:3px;padding:3px 6px}
  #mbar .lbl{font-size:9px}#mbar .track{height:4px}
  #mtouch{bottom:calc(152px + env(safe-area-inset-bottom,0px));grid-template-columns:repeat(2,50px);gap:6px}#mtouch button{width:50px;height:50px;font-size:10px}
  #msub{bottom:calc(10px + env(safe-area-inset-bottom,0px));width:min(560px,calc(100vw - 320px))}#msub .tx{font-size:13px}#msub .portrait{width:48px;height:58px}
  #mprompt{top:calc(50% + 26px)}
  #mtitle{font-size:22px}#mtitle svg{height:34px!important}
  #mplaque{top:calc(8px + env(safe-area-inset-top,0px));bottom:auto;left:50%;right:auto;transform:translateX(-50%);width:min(460px,calc(100vw - 260px));max-height:calc(100vh - 20px);overflow:auto;font-size:13px}
  #mdlg{bottom:calc(6px + env(safe-area-inset-bottom,0px));max-height:calc(100vh - 16px);overflow:auto;padding:8px 12px;gap:10px}
  #mdlg .portrait{width:56px;height:67px}#mdlg .tx{font-size:14px;min-height:0}#mdlg .opts button{font-size:13.5px;padding:8px 10px}#mdlg .opts button small{font-size:11px}
  #mtbl{flex-wrap:nowrap;max-height:calc(100vh - 12px);padding:8px 10px;gap:10px}
  #mtbl canvas{width:calc(100vh - 32px);max-width:48vw;flex:none}
  #mtbl .side{min-width:0;font-size:13px;max-height:calc(100vh - 32px);overflow:auto}#mtbl .side p{font-size:13px;margin:0 0 6px}#mtbl h4{font-size:20px}
  #mtbl .btn{padding:8px 10px}
  #mscreen .card{max-height:calc(100vh - 16px)}#mscreen h2{font-size:24px}
  #mmap{width:min(360px,calc(100vh - 30px))}
}

@media (pointer:coarse){#mbar{bottom:calc(150px + env(safe-area-inset-bottom,0px))}}
@media (max-width:760px){#mobj .rn{font-size:18px}#mtitle{font-size:26px}#msub .tx{font-size:14px}#msub{bottom:calc(170px + env(safe-area-inset-bottom,0px))}#mplaque{top:auto;bottom:calc(230px + env(safe-area-inset-bottom,0px))}#mscreen h2{font-size:28px}#mdlg .portrait{width:64px;height:77px}#mdlg .tx{font-size:15px}}
`;
const st=document.createElement('style');st.textContent=css;document.head.appendChild(st);
const hudEl=document.createElement('div');hudEl.id='mhud';
hudEl.innerHTML=`<div id="mlensv"></div><div id="mind"></div>
<div id="mobj"><div class="ch" id="mchap"></div><div class="rn" id="mroom"></div><ul id="mlist"></ul></div>
<div id="mbar" class="framed"><div class="lbl"><span>Дефект</span><span id="mmana" class="mono"></span></div><div class="track"><div class="fill" id="mfill"></div></div>
<div class="lbl"><span>Ясность</span><span id="mclar" class="mono"></span></div><div class="track"><div class="fill" id="mcfill" style="background:linear-gradient(90deg,#2d6a8f,#7fd0ff 70%,#e2f6ff);box-shadow:0 0 10px #7fd0ff"></div></div>
<div class="ab"><span id="ab-blink"><kbd>ПКМ</kbd>Рывок</span><span id="ab-lens" class="off"><kbd>V</kbd>Линза</span><span id="ab-decoy" class="off"><kbd>G</kbd>Зеркало σ</span><span><kbd>F</kbd>Действие</span></div></div>
<div id="mlect" class="framed"></div><div id="mprompt"></div><div id="msub"></div><div id="mbark"></div><div id="mtitle"></div><div id="mtoast"></div>
<div id="mplaque" class="framed"><div class="hd" id="mpl-hd"></div><p id="mpl-x"></p><div class="k" id="mpl-k"></div></div>
<div id="mtouch"><button id="mt-blink">Рывок</button><button id="mt-decoy">σ</button><button id="mt-lens">Линза</button><button id="mt-act" class="act">F</button><button id="mt-run">Бег</button><button id="mt-map">Карта</button><button id="mt-crouch">Присесть</button></div>
<div id="mrot"><div>⟲</div><p>Поверните телефон горизонтально — так виден весь город.</p><button class="btn" id="mrot-x">Играть так</button></div>
<button class="btn" id="mpause">II</button>`;
document.getElementById('ui').appendChild(hudEl);
const flash=document.createElement('div');flash.id='mflash';document.body.appendChild(flash);
const screen=document.createElement('div');screen.id='mscreen';document.body.appendChild(screen);
const dlg=document.createElement('div');dlg.id='mdlg';dlg.className='framed';document.body.appendChild(dlg);
const kleinC=document.createElement('canvas');kleinC.id='mklein';kleinC.style.cssText='position:fixed;inset:0;width:100%;height:100%;pointer-events:none;z-index:2;opacity:0;transition:opacity .3s';document.body.appendChild(kleinC);
const mapC=document.createElement('canvas');mapC.id='mmap';mapC.width=1040;mapC.height=1040;document.body.appendChild(mapC);
const $=id=>document.getElementById(id);

// ═══════════════ кампания и состояние ═══════════════
const CAMP_KEY='p5-campaign',SAVE_KEY='p5-save';
let campaign={unlocked:0,lemmas:{},alerts:0,sleeps:0,bodies:0,decoy:0,met:{}};
try{const c=JSON.parse(localStorage.getItem(CAMP_KEY)||'null');if(c)campaign={...campaign,...c};}catch(_){}
function saveCampaign(){try{localStorage.setItem(CAMP_KEY,JSON.stringify(campaign));}catch(_){}}
const CHS=STORY.chapters;
let S=null,active=false,aiming=false,aimMode='blink',mapOn=false,LV=null;
const CH=()=>CHS[S.ch];
function fresh(chIdx){
  const ch=CHS[chIdx];LV=LEVELS[ch.id]();const A=LV.A;
  const s={ch:chIdx,A,mana:0.5,clar:1,lensOn:false,got:{},lit:A.ROOMS?A.ROOMS.map(r=>r.lit0):[],visited:[],room:-1,time:0,
    stats:{alerts:0,sleeps:0,bodies:0,blinks:0},flags:{},paused:true,over:false,subs:[],plaqueT:0,decoy:null,dlg:false,
    abil:{...LV.abil},items:LV.items.map(it=>({...it})),guards:[]};
  if(chIdx>=3&&campaign.decoy)s.abil.decoy=true;
  if(ch.id==='ch4'||ch.id==='ch5')s.abil.decoy=true;
  S=s;s.c=A.init();
  s.items.forEach(it=>{const lookAt=it.face||(A.kind==='flat'?null:(A.ROOMS&&A.roomOf(it.pos)>=0?A.ROOMS[A.roomOf(it.pos)].c:null));
    if(A.kind==='flat'){it.F=I4();return;}
    const fwd=lookAt?dirTo(it.pos,lookAt):perpAt(it.pos,[1,0,0,0]);it.F=frameAt(it.pos,fwd,A.kind==='plane'?[0,0,1,0]:A.kind==='house'?A.up(it.pos):null);
    it.room=A.ROOMS?A.roomOf(it.pos):-1;it.light=A.kind==='rooms'&&it.room>=0?A.ROOMS[it.room].c:(A.kind==='flat'?null:advancePose(it.pos,A.up(it.pos),0.55).p);});
  s.guards=LV.guards.map((g,i)=>new Guard(g,i));
  s.start=A.pos();
  return s;}
function serialize(){return JSON.stringify({v:2,ch:S.ch,c:S.c,mana:S.mana,abil:S.abil,got:S.got,lit:S.lit,
  clar:S.clar,guards:S.guards.map(x=>x.toJSON()),visited:S.visited,time:S.time,stats:S.stats,flags:S.flags,escape:S.escape||null,stage:S.stage||0,race:S.race||null,straight:S.straight||0,choice:S.choice||null});}
function deserialize(str){const o=JSON.parse(str);if(o.v!==2)return null;const s=fresh(o.ch);
  Object.assign(s,{c:o.c,mana:o.mana,clar:o.clar??1,abil:o.abil,got:o.got,lit:o.lit,visited:o.visited,time:o.time,stats:o.stats,flags:o.flags,escape:o.escape||null,stage:o.stage||0,race:o.race||null,straight:o.straight||0,choice:o.choice||null});
  if(LV.restore)LV.restore(s,o);
  o.guards.forEach((gj,i)=>{const G=s.guards[i];if(!G)return;Object.assign(G,gj);G.scan=null;if(G.state==='chase'){G.state='search';G.timer=0;}G.alert=Math.min(G.alert,0.6);});
  s.room=-1;return s;}
function save(){try{localStorage.setItem(SAVE_KEY,serialize());toast('Сохранено');}catch(_){toast('Сохранить не удалось');}}
function hasSave(){try{const o=JSON.parse(localStorage.getItem(SAVE_KEY)||'null');return !!o&&o.v===2;}catch(_){return false;}}
function load(){try{const s=localStorage.getItem(SAVE_KEY);if(!s)return false;const n=deserialize(s);if(!n)return false;S=n;ui.obj();toast('Загружено');return true;}catch(e){console.error(e);return false;}}

// ───────── реплики ─────────
function lineOf(key){return (CH().lines||{})[key];}
function say(key){const L=typeof key==='string'?lineOf(key):key;if(!L)return;
  if(typeof key==='string'){if(S.flags['said:'+key])return;S.flags['said:'+key]=1;}
  for(const [who,text] of L)S.subs.push({who,text,dur:Math.max(4.5,text.length*0.06)});}
let toastT=0;function toast(t){const e=$('mtoast');e.textContent=t;e.style.opacity=1;toastT=performance.now()+1800;}
let barkT=0;
function bark(G,type){const now=performance.now();if(now<barkT||now<G.barkT)return;
  const p=S.A.pos();if(hyperbolicDistance(p,G.pos)>3.2)return;
  const B=(G.kassel?STORY.kasselBarks:STORY.barks)[type];if(!B)return;const t=B[Math.floor(Math.random()*B.length)];
  const e=$('mbark');e.innerHTML=`<b>${G.name}</b>«${t}»`;e.style.opacity=1;clearTimeout(bark.t);bark.t=setTimeout(()=>e.style.opacity=0,2600);
  barkT=now+2600;G.barkT=now+(type==='patrol'?14000:6000);}
function speakerHTML(who,big){if(who==='—')return '';return PORTRAITS.svg(who,'portrait');}
// модальная сцена: реплики по очереди; затем cb
function scene(lines,cb){S.dlg=true;aiming=false;try{if(document.pointerLockElement)document.exitPointerLock();}catch(_){}
  let i=0;const next=()=>{if(i>=lines.length){dlg.classList.remove('on');S.dlg=false;lock();cb&&cb();return;}
    const [who,text]=lines[i++];const inf=who==='—'?null:PORTRAITS.info(who);if(inf)campaign.met[who]=1;
    dlg.innerHTML=`${inf?PORTRAITS.svg(who,'portrait'):''}<div class="bd">${inf?`<div class="nm">${inf.name}</div><div class="sb">${inf.sub}</div>`:''}
      <div class="tx${inf?'':' narr'}">${text}</div><div class="nx">Пробел / щелчок — дальше</div></div>`;
    dlg.classList.add('on');dlg.onclick=next;};
  dlg._next=next;next();}
function choose(who,text,opts,cb){S.dlg=true;const inf=PORTRAITS.info(who);
  dlg.innerHTML=`${PORTRAITS.svg(who,'portrait')}<div class="bd"><div class="nm">${inf.name}</div><div class="sb">${inf.sub}</div><div class="tx">${text}</div>
    <div class="opts">${opts.map((o,i)=>`<button data-i="${i}">${o.t}${o.d?`<small>${o.d}</small>`:''}</button>`).join('')}</div></div>`;
  dlg.classList.add('on');dlg.onclick=null;dlg._next=null;
  dlg.querySelectorAll('button').forEach(b=>b.addEventListener('click',e=>{e.stopPropagation();dlg.classList.remove('on');S.dlg=false;cb(+b.dataset.i);}));
  const f=dlg.querySelector('button');if(f)f.focus({preventScroll:true});}

// ═══════════════ игровой цикл ═══════════════
const BLINK_MAX=1.7,BLINK_COST=0.25,DECOY_COST=0.35,REGEN_CAP=0.5;
function aimTarget(){const A=S.A,p=A.pos(),f=A.kind==='plane'?(()=>{const c=S.c;return tangent(apply(mul(mul(c.G,c.T),boostZ(c.h)),[Math.cos(c.yaw),Math.sin(c.yaw),0,0]),p);})():tangent(A.basis(2),p);
  const free=A.freeDist(p,f,BLINK_MAX+0.2);const s=clamp(Math.min(free,BLINK_MAX+0.2)-0.16,0,BLINK_MAX);return {s,pt:advancePose(p,f,s).p,f};}
function toggleLens(){if(!S.abil.lens){toast('Линзы нет');return;}
  if(S.lensOn){S.lensOn=false;LV.onLensOff&&LV.onLensOff();return;}
  if(S.clar<0.05){toast('Ясность на исходе');return;}S.lensOn=true;kasselFeels();if(!S.flags.lensFirst){S.flags.lensFirst=1;LV.onLensOn&&LV.onLensOn();}}
function kasselFeels(){for(const G of S.guards)if(G.kassel&&!G.sleep&&hyperbolicDistance(G.pos,S.A.pos())<2.4){
  G.alert=Math.max(G.alert,0.7);G.lastSeen=S.A.pos();if(G.state!=='chase'){G.state='search';G.goal=S.A.pos();G.timer=0;G.scan=null;}bark(G,'suspect');
  if(!S.flags.kfeel){S.flags.kfeel=1;say('kassel');}}}
function doBlink(){if(!S.abil.blink)return;const b=aimTarget();if(b.s<0.12)return;
  if(S.mana<BLINK_COST){toast('Не хватает дефекта');return;}
  S.mana-=BLINK_COST;S.A.blink(b.s);S.stats.blinks++;
  flash.style.transition='none';flash.style.opacity=1;requestAnimationFrame(()=>{flash.style.transition='opacity .35s';flash.style.opacity=0;});
  AU.blink();noise(b.pt,0.45);kasselFeels();}
function doDecoy(){if(!S.abil.decoy){toast('Зеркала σ ещё нет');return;}const b=aimTarget();
  if(S.mana<DECOY_COST){toast('Не хватает дефекта');return;}
  S.mana-=DECOY_COST;let pt=b.pt;if(S.A.constrain)pt=S.A.constrain(pt);S.decoy={pos:pt,t:6,F:frameAt(pt,dirTo(pt,S.A.pos()),S.A.kind==='plane'?[0,0,1,0]:null),nt:0};
  AU.mirror();kasselFeels();}
function noise(at,loud){if(campaign.lecturer)return;for(const G of S.guards){if(G.sleep||G.passive)continue;const d=hyperbolicDistance(G.pos,at),sh=Math.sinh(d),h=loud/(1+sh*sh);
  if(h>0.08){G.alert=clamp(G.alert+0.6*h,0,1);G.heard=at.slice();if(G.state==='patrol'&&G.alert>0.15){G.state='suspect';G.timer=0;G.goal=at.slice();G.scan=null;bark(G,'suspect');}}}}
function visibleItems(){return S.items.filter(it=>!S.got[it.id]&&(!it.cond||it.cond(S)));}
function interactTarget(){const A=S.A,p=A.pos();
  for(const G of S.guards){if(G.sleep||G.state==='chase')continue;const d=hyperbolicDistance(p,G.pos);
    if(d<0.45){const ang=Math.acos(clamp(md(G.dir,dirTo(G.pos,p)),-1,1));
      if(ang>G.fov/2*0.85||G.alert<0.35)return G.kassel?{type:'none',label:'Кассель не спит: маятник качается и во сне'}:{type:'guard',G,label:'Усыпить стража'};}}
  {let best=null,bd=1e9;for(const it of visibleItems()){if(it.kind===5||it.inert)continue;const dd=A.dist(p,it.pos),rr=it.kind===16&&it.puzzle?0.5:(it.rad||0.3);if(dd<rr&&dd/rr<bd){bd=dd/rr;best=it;}}const it=best;if(it)
    return {type:'item',it,label:it.kind===19?'Посмотреть в трубу':it.kind===4&&!it.name&&!(STORY.records||{})[it.doc]?'Прочесть: '+(((CH().docs||{})[it.doc]||{}).t||'запись'):it.kind===16&&it.puzzle?it.name:it.kind===16&&it.talk?'Осмотреть: '+it.name:it.kind===13?'Обмерить '+it.name:it.kind===4&&STORY.records&&STORY.records[it.doc]?'Прочесть запись вычеркнутого':it.kind===17?(S.flags[it.puzzle+'Done']?'Чертёжный стол (решено)':'Чертёжный стол: '+it.name):it.talk?(it.kind===9?'Коснуться Машины':'Говорить: '+it.name):it.kind===2?'Прочесть лемму':it.kind===7?'Взять крупицу дефекта':it.kind===12?'Снять показания':it.kind===15?(/^post/.test(it.id)?'Отметить веху '+(+it.id.slice(4)+1):'Коснуться камня'):'Взять: '+it.name};}
  if(A.lights){const r=S.room;if(A.lampNear(r,p))return {type:'lamp',r,label:S.lit[r]?'Погасить лампу':'Зажечь лампу'};}
  return null;}
function interact(){const t=interactTarget();if(!t||t.type==='none')return;
  if(t.type==='guard'){t.G.sleep=true;t.G.alert=0;t.G.state='sleep';S.stats.sleeps++;AU.sleep();say('sleep');}
  else if(t.type==='item'){const it=t.it;
    if(it.kind===16&&it.puzzle){say('door');openTable(it.puzzle,()=>{S.flags[it.puzzle+'Done']=1;AU.pick();LV.onSolve&&LV.onSolve(it.puzzle);ui.obj();save();});return;}
    if(it.kind===17){if(it.req&&!it.req(S)){say(it.reqLine);return;}if(S.flags[it.puzzle+'Done']){toast('Задача уже решена');return;}openTable(it.puzzle,()=>{S.flags[it.puzzle+'Done']=1;AU.pick();LV.onSolve&&LV.onSolve(it.puzzle);ui.obj();save();});return;}
    if(it.lock&&!S.flags[it.lock+'Done']){say('locked');toast('Заперто');return;}
    if(it.talk){if(!it.keep)S.got[it.id]=1;ui.obj();LV.onTalk&&LV.onTalk(it.id);return;}
    S.got[it.id]=1;AU.pick();
    if(it.kind===2){campaign.lemmas[it.lemma]=1;saveCampaign();showLemma(it.lemma);}
    else if(it.kind===7){S.mana=Math.min(1,S.mana+0.5);toast('Дефект +0,5');}
    else if(it.kind===3){S.abil.lens=true;ui.obj();say('pick:lens');LV.afterPickLens&&LV.afterPickLens();save();}
    else if(it.kind===4){const R=(STORY.records||{})[it.doc];const D=(CH().docs||{})[it.doc]||R;if(R){campaign.records={...(campaign.records||{}),[it.doc]:1};saveCampaign();}if(D)showPlaque(D);say('pick:'+it.id);save();}
    else if(it.kind===12){toast(it.name+': отвесно, 90°');}
    else if(it.kind===15&&!/^post/.test(it.id)){toast('Межевой камень: знак Эллиптиков');}
    ui.obj();LV.onPick&&LV.onPick(it.id);}
  else if(t.type==='lamp'){S.lit[t.r]=!S.lit[t.r];AU.lamp();}}
function showPlaque(L,by){$('mpl-hd').innerHTML=(by?PORTRAITS.svg(by,'portrait'):'')+`<div><h4>${L.t}</h4>${by?`<div class="by">${PORTRAITS.info(by).name} · ${PORTRAITS.info(by).sub}</div>`:''}</div>`;
  $('mpl-x').innerHTML=L.x+(L.pr?`<details style="margin-top:6px"><summary style="cursor:pointer;color:var(--brass);font-size:12px">Доказательство в строку</summary><span style="font-size:13.5px">${L.pr}</span></details>`:'');$('mpl-k').textContent=by?'Лемма записана в журнал (Esc → Леммы)':'';$('mplaque').style.display='block';S.plaqueT=13;}
function showLemma(id){const L=STORY.lemmas[id];if(L)showPlaque({...L,pr:(STORY.proofs||{})[id]},L.by);}
function readInput(dt){
  const run=keys.has('ShiftLeft')||keys.has('ShiftRight');
  const f=(keys.has('KeyW')||keys.has('ArrowUp')?1:0)-(keys.has('KeyS')||keys.has('ArrowDown')?1:0)+joy[1];
  const s=(keys.has('KeyD')?1:0)-(keys.has('KeyA')?1:0)+joy[0];
  const crouchCh=S&&(CH().id==='prologue'||CH().id==='ch4'),crouch=crouchCh&&(keys.has('ControlLeft')||keys.has('ControlRight'));if(S)S.crouch=crouch;
  const u=(keys.has('Space')?1:0)-(keys.has('KeyC')||(!crouchCh&&keys.has('ControlLeft'))?1:0)+vbtn;
  const turn=(keys.has('ArrowRight')?1:0)-(keys.has('ArrowLeft')?1:0);
  const roll=(keys.has('KeyE')?1:0)-(keys.has('KeyQ')?1:0);
  const lx=look[0]*0.0026+turn*1.6*dt,ly=look[1]*0.0026;look=[0,0];
  const moving=Math.min(1,Math.hypot(f,s,u));
  return {f,s,u,lx,ly,roll,run:run&&!crouch,moving,crouch,sp:(run&&!crouch?1.15:0.45)*(crouch?0.55:1)*dt*(S.A.kind==='flat'?1.3:1)};}
function update(dt){
  const A=S.A;S.time+=dt;
  const inp=readInput(dt);A.move(dt,inp);
  const p=A.pos(),r=A.roomOf(p);
  if(r!==S.room){S.room=r;const nm=A.roomName(r);if(nm){$('mroom').textContent=nm;if(!S.visited.includes(r)){S.visited.push(r);roomTitle(nm);}}
    if(A.lights&&r>=0&&!S.lit[r])say('dark');LV.onRoom&&LV.onRoom(r);ui.obj();}
  if(S.lensOn){S.clar-=0.07*dt;if(S.clar<=0){S.clar=0;S.lensOn=false;LV.onLensOff&&LV.onLensOff();}}
  else S.clar=Math.min(1,S.clar+0.035*dt);
  if(S.mana<REGEN_CAP)S.mana=Math.min(REGEN_CAP,S.mana+0.03*dt);
  if(inp.run&&inp.moving>0.1)noise(p,0.9*dt*6);
  LV.tick&&LV.tick(dt,p);
  if(S.graceT>0)S.graceT-=dt;
  if(S.decoy){const D=S.decoy;D.t-=dt;D.nt-=dt;if(D.nt<=0){D.nt=0.8;noise(D.pos,0.5);}if(D.t<=0)S.decoy=null;}
  const lightF=A.lightF(r),motionF=inp.moving>0.1?(inp.run?1.4:1):0.6;
  let maxA=0;
  for(const G of S.guards){if(G.sleep)continue;updateGuard(G,dt,p,lightF,motionF);maxA=Math.max(maxA,G.alert);}
  S.maxA=maxA;
  for(const it of visibleItems())if(it.kind===5&&A.dist(p,it.pos)<0.22){
    if(it.fin){ending(S.escape.id,S.escape.score);return;}
    if(!it.exit||it.exit(S)){if(LV.onExit){if(!S.flags.exiting){S.flags.exiting=1;LV.onExit();}}else completeChapter();}else say('early');}
  if(S.subs.length){const sub=S.subs[0];if(!sub.shown){sub.shown=1;if(sub.who==='nikolai'&&!S.flags.motif){S.flags.motif=1;AU.nikolai();}const inf=sub.who==='—'?null:PORTRAITS.info(sub.who);
      $('msub').innerHTML=`${inf?PORTRAITS.svg(sub.who,'portrait'):''}<div class="tx">${inf?`<span class="who">${inf.name}</span>`:''}${sub.text}</div>`;$('msub').style.opacity=1;}
    sub.dur-=dt;if(sub.dur<=0){S.subs.shift();$('msub').style.opacity=0;}}
  if(S.plaqueT>0){S.plaqueT-=dt;if(S.plaqueT<=0)$('mplaque').style.display='none';}
}
function updateGuard(G,dt,p,lightF,motionF){
  const sc=campaign.lecturer||G.passive?0:G.perceive(p,lightF,motionF)*(S.graceT>0?0.12:1);G.sees=sc;
  if(sc>0){G.alert=clamp(G.alert+dt*RATE*sc*(G.kassel?1.3:1),0,1);G.lastSeen=p.slice();G.seenAgo=0;}
  else{G.seenAgo+=dt;G.alert=clamp(G.alert-dt*(G.state==='chase'?0.10:0.22),0,1);}
  if(S.decoy&&G.state!=='chase'){const dsc=G.perceive(S.decoy.pos,1,1);if(dsc>0){G.alert=Math.min(0.9,G.alert+dt*RATE*dsc);G.goal=S.decoy.pos.slice();
    if(G.state==='patrol'||G.state==='return'){G.state='suspect';G.timer=0;G.scan=null;}
    if(hyperbolicDistance(G.pos,S.decoy.pos)<0.35){bark(G,'decoy');S.decoy=null;}}}
  for(const H of S.guards)if(H!==G&&H.sleep&&!H.found&&G.sees_(H.pos,2.6)){H.found=true;S.stats.bodies++;
    G.alert=Math.max(G.alert,0.75);G.state='search';G.goal=H.pos.slice();G.timer=0;G.scan=null;AU.alert();bark(G,'body');}
  if(G.alert>=1&&G.state!=='chase'){G.state='chase';G.scan=null;S.stats.alerts++;if(G.kassel)S.stats.kchase=(S.stats.kchase||0)+1;AU.alert();bark(G,'chase');say('seen');
    for(const H of S.guards)if(H!==G&&!H.sleep&&!H.passive&&hyperbolicDistance(H.pos,G.pos)<3){H.alert=Math.max(H.alert,0.7);if(H.state!=='chase'){H.state='search';H.goal=p.slice();H.timer=0;H.scan=null;}}}
  const dP=hyperbolicDistance(G.pos,p);
  switch(G.state){
    case 'patrol':{
      if(G.alert>0.3){G.state='suspect';G.timer=0;G.goal=(G.lastSeen||G.heard||p).slice();G.scan=null;bark(G,'suspect');break;}
      if(G.wait>0){G.wait-=dt;G.look(dt);if(G.wait<=0)G.scan=null;if(Math.random()<dt*0.02)bark(G,'patrol');break;}
      const w=G.route[G.wp];
      if(G.moveTo(w.p,0.28,dt)){G.wait=w.wait;G.wp=(G.wp+1)%G.route.length;}
      if(S.A.lights){const gr=S.A.roomOf(G.pos);if(gr>=0&&S.A.ROOMS[gr].lit0&&!S.lit[gr]&&hyperbolicDistance(G.pos,S.A.ROOMS[gr].c)<0.55){S.lit[gr]=true;G.alert=Math.max(G.alert,0.2);AU.lamp();bark(G,'lamp');}}
      break;}
    case 'suspect':{G.timer+=dt;if(G.goal)G.turn(dirTo(G.pos,G.goal),dt,3);
      if(G.timer>0.9&&G.goal&&hyperbolicDistance(G.pos,G.goal)>0.3)G.moveTo(S.A.nav(G.pos,G.goal),0.22,dt);
      if(G.sees>0&&G.lastSeen)G.goal=G.lastSeen.slice();
      if(G.alert<0.12&&G.timer>3){G.state='return';G.scan=null;}break;}
    case 'chase':{const tg=G.seenAgo<0.2?p:(G.lastSeen||p);G.moveTo(S.A.nav(G.pos,tg),0.62,dt);
      if(dP<CATCH)caught(G);
      if(G.seenAgo>3.2){G.state='search';G.goal=(G.lastSeen||p).slice();G.timer=0;G.scan=null;G.alert=Math.min(G.alert,0.85);bark(G,'lost');}break;}
    case 'search':{G.timer+=dt;if(G.goal&&hyperbolicDistance(G.pos,G.goal)>0.25&&G.timer<12)G.moveTo(S.A.nav(G.pos,G.goal),0.40,dt);else G.look(dt);
      if(G.timer>13||(G.alert<0.1&&G.timer>6)){G.state='return';G.scan=null;}break;}
    case 'return':{const w=G.route[G.wp];if(G.moveTo(S.A.nav(G.pos,w.p),0.30,dt))G.state='patrol';if(G.alert>0.3){G.state='suspect';G.timer=0;G.goal=(G.lastSeen||p).slice();}break;}
  }
}
function caught(G){if(S.over)return;
  if(LV.softCatch&&!S.got.lens&&!S.flags.warned&&!G.kassel){S.flags.warned=1;
    const e=$('mbark');e.innerHTML=`<b>${G.name}</b>«Архив закрыт для младших чертёжников».`;e.style.opacity=1;setTimeout(()=>e.style.opacity=0,3000);
    S.c=S.A.init();for(const H of S.guards){H.alert=0;H.state='return';H.scan=null;}say('warned');return;}
  S.over=true;AU.fail();
  screenShow(`<div class="ch">${CH().n} · провал</div><h2>Вас схватили</h2><p>${G.name} держит вас за плечо. ${G.kassel?'«Измерено», — говорит он и останавливает маятник.':'«Храни Прямизну», — шепчет он, будто извиняется.'}</p>
  <div class="q">${STORY.epilogueQuote}</div>
  <div class="row">${hasSave()?'<button class="btn main" data-a="load">Загрузить сохранение</button>':''}<button class="btn${hasSave()?'':' main'}" data-a="restart">Начать главу заново</button><button class="btn" data-a="menu">В меню</button></div>`);}
function failScreen(F){if(S.over)return;S.over=true;AU.fail();
  screenShow(`<div class="ch">${CH().n} · провал</div><h2>${F.t}</h2><p>${F.x}</p>
  <div class="row">${hasSave()?'<button class="btn main" data-a="load">Загрузить сохранение</button>':''}<button class="btn${hasSave()?'':' main'}" data-a="restart">Начать главу заново</button><button class="btn" data-a="menu">В меню</button></div>`);}
function completeChapter(){if(S.over)return;S.over=true;AU.win();
  const st=S.stats;campaign.alerts+=st.alerts;campaign.sleeps+=st.sleeps;campaign.bodies+=st.bodies;campaign.kchase=(campaign.kchase||0)+(st.kchase||0);
  campaign.unlocked=Math.max(campaign.unlocked,Math.min(S.ch+1,CHS.length-1));saveCampaign();
  try{localStorage.removeItem(SAVE_KEY);}catch(_){}
  const tm=Math.floor(S.time/60)+':'+String(Math.floor(S.time%60)).padStart(2,'0');
  const lem=S.items.filter(i=>i.kind===2),lg=lem.filter(i=>S.got[i.id]).length;
  const rank=st.alerts===0&&st.sleeps===0?'Призрак: вас не видели, никто не усыплён':st.alerts===0?'Тень: ни одной тревоги':st.alerts<3?'Свидетели есть, но вы ушли':'Тревога гремит до самого Собора';
  const nx=CHS[S.ch+1];const ck=(STORY.checks||{})[CH().id];
  screenShow(`<div class="ch">${CH().n} · пройдена</div><h2>${CH().title}</h2><p>${CH().end}</p>
  ${ck?`<div class="quiz"><div class="ch">Проверка</div><p><b>${ck.q}</b></p><div class="chk">${ck.a.map((t,i)=>`<button class="btn" data-a="check" data-i="${i}">${t}</button>`).join('')}</div><p class="ce" hidden></p></div>`:''}
  ${S.guards.length?`<div class="rank">${rank}</div>`:''}
  <div class="stats"><span>Время</span><span>${tm}</span>${S.guards.length?`<span>Тревоги</span><span>${st.alerts}</span><span>Усыплено стражей</span><span>${st.sleeps}</span><span>Найдено спящих</span><span>${st.bodies}</span>`:''}
  <span>Леммы главы</span><span>${lg} / ${lem.length}</span><span>Леммы всего</span><span>${Object.keys(campaign.lemmas).length} / ${Object.keys(STORY.lemmas).length}</span></div>
  <div class="row">${nx?`<button class="btn main" data-a="next">${nx.n}: ${nx.title}</button>`:''}<button class="btn" data-a="restart">Переиграть главу</button><button class="btn" data-a="menu">В меню</button></div>`);}
function roomTitle(n){if(LV.roomTitles===false)return;const e=$('mtitle');e.innerHTML=`<small>${CH().title}</small>${FONT.svg(n,{h:'50px'})}<i></i>`;e.style.opacity=1;clearTimeout(roomTitle.t);roomTitle.t=setTimeout(()=>e.style.opacity=0,2200);}

// ───────── диспут и концовки ─────────
function debate(){let i=0,score=0;
  scene(STORY.debateIntro,()=>{S.dlg=true;const ask=()=>{if(i>=STORY.debate.length){finale(score);return;}
    const D=STORY.debate[i++];
    choose('euclid',D.claim,D.answers,k=>{const ok=!!D.answers[k].ok;if(ok)score++;scene([['euclid',ok?D.yes:D.no]],ask);});};ask();});}
function finale(score){const lem=Object.keys(campaign.lemmas).length,win=score===STORY.debate.length,secret=win&&lem>=12;
  S.flags.score=score;S.flags.secret=secret?1:0;
  scene([...(win?STORY.debateWin:STORY.debateLose),...STORY.truth,...CH().lines.nodes],()=>{S.flags.nodes=1;S.A.unseal&&S.A.unseal('sanct','heart');
    if(!secret)toast(win?'Пустой стол ждёт: нужно не меньше 12 лемм ('+lem+')':'Евклид не убеждён до конца — пустой стол закрыт');ui.obj();save();lock();});}
// стелс-побег после диспута (концепт: «диспут + стелс-побег»)
function startEscape(id,score){S.escape={id,score};
  if(id==='straight'){S.abil.lens=false;S.lensOn=false;}
  for(const G of S.guards){if(G.sleep)continue;
    if((id==='postulate'&&!G.kassel)||(G.kassel&&S.flags.kgive)){G.passive=true;G.state='return';G.alert=0;continue;}G.passive=false;
    G.alert=id==='straight'?0.3:0.5;G.state='search';G.goal=S.A.pos();G.timer=0;G.scan=null;}
  S.graceT=4.5;ui.obj();scene(S.flags.kgive?STORY.escape[id].filter(l=>l[0]!=='kassel').map(l=>id==='postulate'&&l[0]==='nikolai'?['nikolai','Никто тебя не держит. Даже он. Иди к Вратам.']:l):STORY.escape[id],()=>{save();toast('Сохранено. Бегите к Воротам');});}
function epiExtra(id,E){const o=[],c=campaign;
  if(id==='straight'&&c.wrote89)o.push(E.wrote89);
  if(id==='curved'&&(c.ch4cost||c.ch3choice==='strike'))o.push(E.cost);
  if(c.ch4choice==='reconf'&&E.reconf)o.push(E.reconf);
  if(c.ch3choice==='evac'&&E.evac)o.push(E.evac);
  if(c.kasselSpared&&E.kassel)o.push(E.kassel);
  if(Object.keys(c.records||{}).length>=6&&E.records)o.push(E.records);
  return o;}
function ending(id,score){S.over=true;AU.win();const E=STORY.endings[id];const st=S.stats;
  campaign.alerts+=st.alerts;campaign.sleeps+=st.sleeps;campaign.bodies+=st.bodies;campaign.ending=id;campaign.endings={...(campaign.endings||{}),[id]:1};saveCampaign();
  const highChaos=campaign.alerts>8||campaign.bodies>3;
  screenShow(`<div class="crest">${emblemSVG()}<div class="ch">Эпилог · концовка</div><span class="fxl">${FONT.svg(E.t,{h:'54px'})}</span></div>
  ${E.x.map(x=>`<p>${x}</p>`).join('')}${epiExtra(id,E).map(x=>`<p>${x}</p>`).join('')}${highChaos?`<p style="color:var(--muted)">${E.chaos}</p>`:''}
  <div class="q">${STORY.epilogueQuote}</div>
  <div class="stats"><span>Тревоги за кампанию</span><span>${campaign.alerts}</span><span>Усыплено стражей</span><span>${campaign.sleeps}</span><span>Леммы</span><span>${Object.keys(campaign.lemmas).length} / ${Object.keys(STORY.lemmas).length}</span><span>Доводы в диспуте</span><span>${score} / ${STORY.debate.length}</span><span>Открыто концовок</span><span>${Object.keys(campaign.endings).length} / 3</span></div>
  <p style="color:var(--muted);font-size:13px">«Пятый Постулат» — игра о геометрии Лобачевского. Все леммы и формулы в ней — настоящие.</p>
  <div class="row"><button class="btn main" data-a="gallery">Портретная галерея</button><button class="btn" data-a="menu">В меню</button></div>`);}


// ═══════════════ чертёжные столы (концепт, §12) ═══════════════
const tbl=document.createElement('div');tbl.id='mtbl';tbl.className='framed';document.body.appendChild(tbl);
function openTable(kind,onWin){S.dlg=true;aiming=false;try{if(document.pointerLockElement)document.exitPointerLock();}catch(_){}
  tbl.innerHTML=`<canvas width="900" height="900"></canvas><div class="side"></div>`;tbl.classList.add('on');
  const cv=tbl.querySelector('canvas'),side=tbl.querySelector('.side');
  const close=won=>{tbl.classList.remove('on');tbl.innerHTML='';S.dlg=false;lock();if(won)onWin();};
  ({gap:puzzleGap,circ:puzzleCirc,square:puzzleSquare,dial:puzzleDial,straightSq:puzzleStraight,breakEdge:puzzleBreak,compat:puzzleCompat})[kind](cv,side,close);}
function boardBG(x,W){x.fillStyle='#0b1d36';x.fillRect(0,0,W,W);x.strokeStyle='rgba(140,190,255,.08)';x.lineWidth=1;
  for(let i=0;i<=W;i+=30){x.beginPath();x.moveTo(i,0);x.lineTo(i,W);x.stroke();x.beginPath();x.moveTo(0,i);x.lineTo(W,i);x.stroke();}}
// П0.3: выпускной чертёж — квадрат по узлам сетки (евклидов город, всё сходится)
function puzzleSquare(cv,side,close){const x=cv.getContext('2d'),W=900,N=8,m=110,st=(W-2*m)/N;let P=[],ok=false;
  side.innerHTML=`<div class="ch">Академия Прямизны · выпускной экзамен</div><h4>Начертить квадрат</h4><p>Отметьте четыре вершины по узлам сетки — по порядку обхода. Стол проверит равенство сторон и углов.</p><p class="st"></p><div class="row"><button class="btn" data-k="r">Стереть</button><button class="btn" data-k="x">Отойти от доски</button></div>`;
  const node=(i,j)=>[m+i*st,m+j*st];
  function ang(a,b,c){const u=[a[0]-b[0],a[1]-b[1]],v=[c[0]-b[0],c[1]-b[1]];return Math.round(Math.acos((u[0]*v[0]+u[1]*v[1])/Math.hypot(...u)/Math.hypot(...v))*180/Math.PI);}
  function draw(){x.fillStyle='#efe6cf';x.fillRect(0,0,W,W);x.strokeStyle='rgba(60,70,110,.18)';x.lineWidth=2;
    for(let i=0;i<=N;i++){x.beginPath();x.moveTo(...node(i,0));x.lineTo(...node(i,N));x.stroke();x.beginPath();x.moveTo(...node(0,i));x.lineTo(...node(N,i));x.stroke();}
    x.strokeStyle='#1b2340';x.lineWidth=5;x.beginPath();P.forEach((q,k)=>{const n=node(...q);k?x.lineTo(...n):x.moveTo(...n);});if(P.length===4)x.closePath();x.stroke();
    P.forEach((q,k)=>{const n=node(...q);x.fillStyle='#8a5f2c';x.beginPath();x.arc(...n,11,0,7);x.fill();});
    if(P.length===4){const V=P.map(q=>node(...q));x.fillStyle='#1b2340';x.font='600 30px IBM Plex Mono, monospace';x.textAlign='center';
      V.forEach((b,k)=>{const a=V[(k+3)%4],c=V[(k+1)%4],cx=(a[0]+c[0])/2,cy=(a[1]+c[1])/2,dx=cx-b[0],dy=cy-b[1],l=Math.hypot(dx,dy)||1;x.fillText(ang(a,b,c)+'°',b[0]+dx/l*52,b[1]+dy/l*52+10);});}}
  function check(){const V=P.map(q=>node(...q)),sides=V.map((a,k)=>Math.hypot(V[(k+1)%4][0]-a[0],V[(k+1)%4][1]-a[1])),angs=V.map((b,k)=>ang(V[(k+3)%4],b,V[(k+1)%4]));
    const stt=side.querySelector('.st');
    if(angs.every(a=>a===90)&&sides.every(l=>Math.abs(l-sides[0])<1)){ok=true;stt.innerHTML=`<b style="color:#9fdc8a">Чертёж принят.</b> 90° + 90° + 90° + 90° = 360°. Нечего исправить.`;AU.pick();setTimeout(()=>close(true),2000);}
    else stt.textContent=angs.every(a=>a===90)?'Углы прямые, но стороны не равны — это прямоугольник. Сотрите и начертите снова.':'Это не квадрат: '+angs.join('° + ')+'°. Сотрите и начертите снова.';}
  cv.addEventListener('pointerdown',e=>{if(ok||P.length>=4)return;const r=cv.getBoundingClientRect(),X=(e.clientX-r.left)/r.width*W,Y=(e.clientY-r.top)/r.height*W;
    const i=Math.round((X-m)/st),j=Math.round((Y-m)/st);if(i<0||j<0||i>N||j>N)return;if(P.some(q=>q[0]===i&&q[1]===j))return;P.push([i,j]);draw();if(P.length===4)check();});
  side.addEventListener('click',e=>{const k=e.target.closest('[data-k]')?.dataset.k;if(k==='x')close(false);if(k==='r'&&!ok){P=[];side.querySelector('.st').textContent='';draw();}});
  draw();}
// 1.5: дверь 359 — замок из четырёх угловых дисков
function puzzleDial(cv,side,close){const x=cv.getContext('2d'),W=900,V=[90,90,90,90];let ok=false;
  side.innerHTML=`<div class="ch">Архив Инквизиции</div><h4>Дверь комнаты 281</h4><p>На двери выбито: «Исправный четырёхугольник: 360°». Каждый диск — угол комнаты. Выставьте углы и поверните ручку.</p>
  <div class="dials">${[0,1,2,3].map(i=>`<div class="row"><span class="mono">угол ${i+1}</span> <button class="btn" data-d="${i}" data-v="-10">−10</button><button class="btn" data-d="${i}" data-v="-1">−1</button><button class="btn" data-d="${i}" data-v="1">+1</button><button class="btn" data-d="${i}" data-v="10">+10</button></div>`).join('')}</div>
  <p class="sum mono"></p><div class="row"><button class="btn main" data-k="open">Повернуть ручку</button><button class="btn" data-k="x">Отойти</button></div><p class="st"></p>`;
  function draw(){x.fillStyle='#14100a';x.fillRect(0,0,W,W);x.strokeStyle='#5a4426';x.lineWidth=6;x.strokeRect(60,60,W-120,W-120);
    V.forEach((v,i)=>{const cx=W*(i%2?0.7:0.3),cy=W*(i<2?0.32:0.68),R=150;
      const g=x.createRadialGradient(cx-40,cy-40,20,cx,cy,R);g.addColorStop(0,'#f2cf8e');g.addColorStop(1,'#7c5426');x.fillStyle=g;x.beginPath();x.arc(cx,cy,R,0,7);x.fill();
      x.strokeStyle='#2a1a08';x.lineWidth=3;for(let a=0;a<=180;a+=10){const t=Math.PI+a*Math.PI/180,l=a%30?14:26;x.beginPath();x.moveTo(cx+Math.cos(t)*(R-6),cy+Math.sin(t)*(R-6));x.lineTo(cx+Math.cos(t)*(R-6-l),cy+Math.sin(t)*(R-6-l));x.stroke();}
      const t=Math.PI+v*Math.PI/180;x.strokeStyle='#14100a';x.lineWidth=7;x.beginPath();x.moveTo(cx,cy);x.lineTo(cx+Math.cos(t)*(R-30),cy+Math.sin(t)*(R-30));x.stroke();
      x.fillStyle='#14100a';x.font='600 40px IBM Plex Mono, monospace';x.textAlign='center';x.fillText(v+'°',cx,cy+70);});
    side.querySelector('.sum').textContent=V.join('° + ')+'° = '+V.reduce((a,b)=>a+b,0)+'°';}
  side.addEventListener('click',e=>{if(ok)return;const b=e.target.closest('button');if(!b)return;
    if(b.dataset.d!=null){const i=+b.dataset.d;V[i]=clamp(V[i]+(+b.dataset.v),1,179);AU.tone(1500,0.03,'square',0.015);draw();return;}
    if(b.dataset.k==='x')return close(false);
    const sorted=V.slice().sort((a,b)=>a-b),sum=V.reduce((a,b)=>a+b,0),stt=side.querySelector('.st');
    if(sorted.join()==='89,90,90,90'){ok=true;stt.innerHTML='<b style="color:#9fdc8a">Щелчок. Низкий гул — и лязг засова.</b> 90° + 90° + 90° + 89° = 359°.';AU.tone(70,0.8,'sawtooth',0.06);setTimeout(()=>close(true),1800);}
    else if(sum===360)stt.textContent='Не открывается. «Исправный четырёхугольник» — но комната №7 исправной не была.';
    else stt.textContent='Не открывается. Ручка не идёт.';});
  draw();}
// 5.10 · Прямизна: тот же квадрат, что на выпускном экзамене
function puzzleStraight(cv,side,close){puzzleSquare(cv,side,close);side.querySelector('.ch').textContent='Сердце Машин · узел Прямизны';
  side.querySelector('h4').textContent='Выровнять все линии';side.querySelector('p').innerHTML='Машина примет только чертёж, в котором нечего исправить: квадрат по узлам сетки. Четыре прямых угла — и город снова будет ровным.';}
// 5.10 · Кривизна: разорвать контуры Машины — вернуть ребру его 72°
function puzzleBreak(cv,side,close){const x=cv.getContext('2d'),W=900,Cx=W/2,R=W*0.36;let A=[90,90,90,90],n=4,ok=false;
  side.innerHTML=`<div class="ch">Сердце Машин · узел Кривизны</div><h4>Разорвать контуры</h4><p>Сечение вокруг одного ребра Цитадели. Машина держит четыре куба по 90° — силой. Нажмите на клин, чтобы разорвать контур и отпустить его угол. Потом закройте ребро столько кубами, сколько их здесь на самом деле.</p>
  <p class="sum mono"></p><div class="row"><button class="btn main" data-k="+">+ куб</button><button class="btn" data-k="x">Отойти от стола</button></div><p class="st"></p>`;
  const draw=()=>{boardBG(x,W);let a0=-90;for(let i=0;i<n;i++){const a=A[i]??72,s0=a0*Math.PI/180,s1=(a0+a)*Math.PI/180;
      x.fillStyle=a===90?'rgba(232,184,102,.35)':'rgba(111,211,255,.28)';x.strokeStyle=a===90?'#e8b866':'#6fd3ff';x.lineWidth=4;
      x.beginPath();x.moveTo(Cx,Cx);x.arc(Cx,Cx,R,s0,s1);x.closePath();x.fill();x.stroke();
      const m=(s0+s1)/2;x.fillStyle='#ece5d6';x.font='600 34px IBM Plex Mono, monospace';x.textAlign='center';x.fillText(a+'°',Cx+Math.cos(m)*R*0.62,Cx+Math.sin(m)*R*0.62+12);
      if(a===90){x.strokeStyle='rgba(255,255,255,.5)';x.setLineDash([10,8]);x.beginPath();x.arc(Cx,Cx,R+22,s0+0.05,s1-0.05);x.stroke();x.setLineDash([]);}a0+=a;}
    const tot=A.slice(0,n).reduce((s,v)=>s+(v??72),0)+Math.max(0,n-A.length)*72;
    if(tot<360){const s0=(a0)*Math.PI/180,s1=270*Math.PI/180;x.fillStyle='rgba(255,90,60,.18)';x.beginPath();x.moveTo(Cx,Cx);x.arc(Cx,Cx,R,s0,s1);x.closePath();x.fill();
      x.fillStyle='#ff8a6a';x.font='600 30px IBM Plex Mono, monospace';const m=(s0+s1)/2;x.fillText('щель '+(360-tot)+'°',Cx+Math.cos(m)*R*0.6,Cx+Math.sin(m)*R*0.6);}
    x.fillStyle='#fff';x.beginPath();x.arc(Cx,Cx,9,0,7);x.fill();
    side.querySelector('.sum').textContent=Array.from({length:n},(_,i)=>(A[i]??72)+'°').join(' + ')+' = '+tot+'°';return tot;};
  cv.addEventListener('pointerdown',e=>{if(ok)return;const r=cv.getBoundingClientRect(),X=(e.clientX-r.left)/r.width*W-Cx,Y=(e.clientY-r.top)/r.height*W-Cx;
    if(Math.hypot(X,Y)>R+30)return;let ang=Math.atan2(Y,X)*180/Math.PI+90;if(ang<0)ang+=360;let a0=0;
    for(let i=0;i<n;i++){const a=A[i]??72;if(ang<a0+a){if(A[i]===90){A[i]=72;AU.tone(220,0.25,'sawtooth',0.05);}break;}a0+=a;}draw();});
  side.addEventListener('click',e=>{const k=e.target.closest('[data-k]')?.dataset.k;if(!k||ok)return;if(k==='x')return close(false);const stt=side.querySelector('.st');
    if(A.some(v=>v===90)){stt.textContent='Машина держит контуры: пока углы 90°, ребро «закрыто» четырьмя кубами. Сначала разорвите контуры.';return;}
    if(n>=5){stt.textContent='Шестой куб не помещается: 6 × 72° = 432°.';return;}
    n++;AU.tone(330,0.2,'triangle',0.04);const tot=draw();
    if(tot===360){ok=true;stt.innerHTML='<b style="color:#9fdc8a">Квинта распадается.</b> 5 × 72° = 360°: у ребра пять кубов, как и было до Машин.';AU.tone(55,1.4,'sawtooth',0.09);setTimeout(()=>close(true),2200);}});
  draw();}
// 5.10 · Пятый постулат: несколько совместимых геометрий — хорды, полюсы, орициклы, дефект, орисферы
function puzzleCompat(cv,side,close){const x=cv.getContext('2d'),W=900,Cx=W/2,R=W*0.38;let st=0,ok=false;
  const pt=a=>[Cx+R*Math.cos(a),Cx+R*Math.sin(a)];const a1=-1.95,a2=-0.6,Pa=pt(a1),Pb=pt(a2);
  const pole=(()=>{const m=(a1+a2)/2,h=Math.cos((a2-a1)/2);return [Cx+R/h*Math.cos(m),Cx+R/h*Math.sin(m)];})();
  const mid=[(Pa[0]+Pb[0])/2,(Pa[1]+Pb[1])/2];
  const steps=[
    {q:'Прямая через две точки абсолюта. В модели Кэли — Клейна прямая — это…',c:[{t:'хорда круга',ok:1,d:'chord'},{t:'дуга, перпендикулярная абсолюту',d:'arc'},{t:'ломаная через центр',d:'broken'}],why:'В модели Кэли — Клейна прямые изображаются хордами; дуги, ортогональные абсолюту, — это модель Пуанкаре.'},
    {q:'Где лежит полюс этой хорды?',c:[{t:'в середине хорды',d:'pmid'},{t:'вне абсолюта, на пересечении касательных',ok:1,d:'pole'},{t:'на самом абсолюте',d:'pon'}],why:'Полюс прямой лежит вне абсолюта: в нём сходятся касательные к абсолюту в концах хорды. Все перпендикуляры к прямой проходят через полюс.'},
    {q:'Какая кривая — орицикл, граница переходного квартала?',c:[{t:'касается абсолюта в одной точке',ok:1,d:'horo'},{t:'целиком внутри, не касаясь',d:'circ'},{t:'пересекает абсолют дважды',d:'equi'}],why:'Орицикл касается абсолюта в одной точке: это «окружность с центром на бесконечности».'},
    {q:'Гиперболический квартал: треугольник с углами 50°, 60°, 40°. Его дефект (а значит, и площадь при k = 1)?',c:[{t:'0°',d:'tri'},{t:'30°, то есть π/6',ok:1,d:'tri'},{t:'150°',d:'tri'}],why:'Дефект = 180° − (50° + 60° + 40°) = 30°. Площадь треугольника равна дефекту: π/6.'},
    {q:'Где поместить евклидов квартал — для тех, кому нужен покой?',c:[{t:'на сфере',d:'regions'},{t:'на эквидистантной поверхности',d:'regions'},{t:'на орисфере',ok:1,d:'regions'}],why:'Внутренняя геометрия орисферы — евклидова (Ф. Л. Вахтер, 1816; Н. И. Лобачевский). Покой не нужно отнимать у кривизны: он в ней уже есть.'}];
  side.innerHTML=`<div class="ch">Сердце Машин · пустой стол</div><h4>Начертить совместимые геометрии</h4><p>Не одну геометрию, а несколько — так, чтобы ни одна не лгала. Каждый шаг — построение в круге Кэли — Клейна.</p><p class="stg mono"></p><p class="q2"></p><div class="opts" style="display:flex;flex-direction:column;gap:6px"></div><p class="st"></p><div class="row"><button class="btn" data-k="x">Отойти от стола</button></div>`;
  const done=new Set();
  function draw(hl){boardBG(x,W);x.strokeStyle='#e8b866';x.lineWidth=4;x.beginPath();x.arc(Cx,Cx,R,0,7);x.stroke();
    const show=d=>done.has(d)||hl===d;
    x.fillStyle='#ece5d6';[Pa,Pb].forEach(q=>{x.beginPath();x.arc(...q,9,0,7);x.fill();});
    x.lineWidth=5;
    if(show('chord')){x.strokeStyle='#6fd3ff';x.beginPath();x.moveTo(...Pa);x.lineTo(...Pb);x.stroke();}
    if(hl==='arc'){x.strokeStyle='#ff8a6a';const d=Math.hypot(pole[0]-Cx,pole[1]-Cx),r=Math.sqrt(d*d-R*R);x.beginPath();x.arc(...pole,r,0,7);x.stroke();}
    if(hl==='broken'){x.strokeStyle='#ff8a6a';x.beginPath();x.moveTo(...Pa);x.lineTo(Cx,Cx);x.lineTo(...Pb);x.stroke();}
    if(show('pole')||hl==='pmid'||hl==='pon'){const q=hl==='pmid'?mid:hl==='pon'?pt((a1+a2)/2):pole;x.fillStyle=hl&&hl!=='pole'?'#ff8a6a':'#d9ccff';x.beginPath();x.arc(...q,12,0,7);x.fill();
      if(show('pole')){x.strokeStyle='rgba(217,204,255,.6)';x.lineWidth=2;x.beginPath();x.moveTo(...Pa);x.lineTo(...pole);x.lineTo(...Pb);x.stroke();
        x.save();x.beginPath();x.arc(Cx,Cx,R,0,7);x.clip();x.setLineDash([8,8]);for(const s of [0.25,0.5,0.75]){const q2=[Pa[0]+(Pb[0]-Pa[0])*s,Pa[1]+(Pb[1]-Pa[1])*s];x.beginPath();x.moveTo(...pole);x.lineTo(pole[0]+(q2[0]-pole[0])*9,pole[1]+(q2[1]-pole[1])*9);x.stroke();}x.setLineDash([]);x.restore();}}
    const ha=1.9,hT=pt(ha);
    if(show('horo')){x.strokeStyle='#9fdc8a';x.lineWidth=4;x.beginPath();x.ellipse(Cx+(hT[0]-Cx)*0.72,Cx+(hT[1]-Cx)*0.72,R*0.28,R*0.21,ha,0,7);x.stroke();}
    if(hl==='circ'){x.strokeStyle='#ff8a6a';x.beginPath();x.arc(Cx+(hT[0]-Cx)*0.5,Cx+(hT[1]-Cx)*0.5,R*0.2,0,7);x.stroke();}
    if(hl==='equi'){x.strokeStyle='#ff8a6a';x.beginPath();x.arc(...pt(ha),R*0.35,0,7);x.stroke();}
    if(show('tri')){const T=[[Cx-60,Cx+40],[Cx+120,Cx+70],[Cx+20,Cx-110]];x.strokeStyle='#d6a35a';x.fillStyle='rgba(214,163,90,.15)';x.lineWidth=4;x.beginPath();T.forEach((q,k)=>k?x.lineTo(...q):x.moveTo(...q));x.closePath();x.fill();x.stroke();
      x.fillStyle='#ece5d6';x.font='600 26px IBM Plex Mono, monospace';x.textAlign='center';x.fillText('δ = 30°',Cx+28,Cx+10);}
    if(done.has('regions')){x.save();x.beginPath();x.arc(Cx,Cx,R,0,7);x.clip();
      x.fillStyle='rgba(111,211,255,.10)';x.beginPath();x.moveTo(...Pa);x.lineTo(...Pb);x.arc(Cx,Cx,R,a2,a1,true);x.fill();
      x.fillStyle='rgba(159,220,138,.16)';x.beginPath();x.ellipse(Cx+(hT[0]-Cx)*0.72,Cx+(hT[1]-Cx)*0.72,R*0.28,R*0.21,ha,0,7);x.fill();x.restore();
      x.fillStyle='#ece5d6';x.font='500 24px Old Standard TT, serif';x.textAlign='center';
      x.fillText('гиперболический район',Cx+(Pa[0]+Pb[0]-2*Cx)*0.9,Cx+(Pa[1]+Pb[1]-2*Cx)*0.95);x.fillText('евклидов квартал (орисфера)',Cx+(hT[0]-Cx)*0.72,Cx+(hT[1]-Cx)*0.72+70);x.fillText('переходная зона',Cx-40,Cx+160);}}
  function ask(){const S0=steps[st];side.querySelector('.stg').textContent='Шаг '+(st+1)+' из '+steps.length;side.querySelector('.q2').innerHTML='<b>'+S0.q+'</b>';
    side.querySelector('.opts').innerHTML=S0.c.map((c,i)=>`<button class="btn" data-o="${i}">${c.t}</button>`).join('');draw();}
  side.addEventListener('pointerover',e=>{const b=e.target.closest('[data-o]');if(b&&!ok)draw(steps[st].c[+b.dataset.o].d);});
  side.addEventListener('click',e=>{const k=e.target.closest('[data-k]')?.dataset.k;if(k==='x')return close(false);const b=e.target.closest('[data-o]');if(!b||ok)return;
    const S0=steps[st],c=S0.c[+b.dataset.o],stt=side.querySelector('.st');
    if(!c.ok){stt.textContent='Это построение лжёт. '+S0.why;AU.tone(110,0.3,'square',0.03);return;}
    done.add(c.d);stt.innerHTML='<span style="color:#9fdc8a">Верно.</span> '+S0.why;AU.pick();st++;
    if(st>=steps.length){ok=true;draw();side.querySelector('.opts').innerHTML='';side.querySelector('.q2').innerHTML='<b>Город становится лоскутным — и ни один лоскут не лжёт.</b>';setTimeout(()=>close(true),3200);}else ask();});
  ask();}
// «Щель»: сколько многогранников с данным двугранным углом закрывают ребро
function puzzleGap(cv,side,close){const stages=[{n:'Прямые додекаэдры Тюрьмы {5,3,4}',a:90},{n:'Кубы Цитадели {4,3,5}',a:72}];let st=0,n=1,lockT=false;
  const x=cv.getContext('2d'),W=900,C=W/2,R=W*0.36;
  side.innerHTML=`<div class="ch">Чертёжный стол</div><h4>Замок-сота</h4><p>Это сечение вокруг одного ребра. Каждый клин — многогранник, его угол — двугранный угол. Сложите вокруг ребра столько многогранников, чтобы не осталось ни щели, ни наложения.</p>
  <p class="stg"></p><p class="sum mono"></p><div class="row"><button class="btn" data-k="-">− многогранник</button><button class="btn main" data-k="+">+ многогранник</button></div><p class="st"></p><div class="row"><button class="btn" data-k="x">Отойти от стола</button></div>`;
  const draw=()=>{const S0=stages[st],a=S0.a,sum=n*a;boardBG(x,W);
    for(let i=0;i<n;i++){const a0=(i*a-90)*Math.PI/180,a1=((i+1)*a-90)*Math.PI/180,over=(i+1)*a>360;
      x.beginPath();x.moveTo(C,C);x.arc(C,C,R,a0,a1);x.closePath();x.fillStyle=over?'rgba(255,90,60,.45)':(i%2?'rgba(80,140,210,.55)':'rgba(120,180,240,.45)');x.fill();
      x.strokeStyle='rgba(230,240,255,.85)';x.lineWidth=3;x.stroke();
      const am=(a0+a1)/2;x.fillStyle='#e8f1ff';x.font='500 30px IBM Plex Mono, monospace';x.textAlign='center';x.fillText(a+'°',C+Math.cos(am)*R*0.62,C+Math.sin(am)*R*0.62+10);}
    if(sum<360){const g0=(sum-90)*Math.PI/180,g1=(270)*Math.PI/180;x.save();x.beginPath();x.moveTo(C,C);x.arc(C,C,R,g0,g1);x.closePath();x.clip();
      x.strokeStyle='rgba(255,120,90,.7)';x.lineWidth=3;for(let k=-W;k<W;k+=22){x.beginPath();x.moveTo(k,0);x.lineTo(k+W,W);x.stroke();}x.restore();
      const gm=(g0+g1)/2;x.fillStyle='#ff9a80';x.font='600 34px IBM Plex Sans, sans-serif';x.fillText('щель '+(360-sum)+'°',C+Math.cos(gm)*R*0.6,C+Math.sin(gm)*R*0.6);}
    x.fillStyle='#d6a35a';x.beginPath();x.arc(C,C,10,0,7);x.fill();x.font='26px IBM Plex Sans';x.fillText('ребро',C,C+44);
    side.querySelector('.stg').innerHTML=`<b>Этап ${st+1} из ${stages.length}:</b> ${S0.n}, двугранный угол ${a}°`;
    side.querySelector('.sum').textContent=`${n} × ${a}° = ${sum}°`+(sum<360?` — не хватает ${360-sum}°`:sum>360?` — наложение ${sum-360}°`:' — ровно полный оборот');};
  side.addEventListener('click',e=>{const k=e.target.closest('[data-k]')?.dataset.k;if(!k||lockT)return;if(k==='x')return close(false);
    n=clamp(n+(k==='+'?1:-1),1,8);draw();const a=stages[st].a;
    if(n*a===360){lockT=true;side.querySelector('.st').innerHTML=`<b style="color:#9fdc8a">Ребро закрыто без щели.</b> ${n} × ${a}° = 360°.`+(st===0?' Следующий этап…':' Замок щёлкает.');AU.pick();
      setTimeout(()=>{lockT=false;if(st+1<stages.length){st++;n=1;side.querySelector('.st').innerHTML='Если бы кубов с углом 72° было четыре, осталась бы щель в 72° (курсовая, п. 6.2).';draw();}else close(true);},1400);}
    else side.querySelector('.st').textContent=n*a<360?'Между многогранниками пустой клин — в такой соте были бы щели.':'Многогранники налезают друг на друга.';});
  draw();}
// «Описание без циркуля»: окружность, орицикл или эквидистанта через три точки (модель Пуанкаре)
function puzzleCirc(cv,side,close){
  const x=cv.getContext('2d'),W=900,C=W/2,R=W*0.45;
  const P=[[-0.42,-0.22],[0.44,-0.18],[0.02,0.34]],found={circle:0,horo:0,equi:0};let prev=null,drag=-1,done=false;
  const toH=z=>{const r2=z[0]*z[0]+z[1]*z[1],k=1/(1-r2);return [2*z[0]*k,2*z[1]*k,(1+r2)*k];};
  const ip=(a,b)=>a[0]*b[0]+a[1]*b[1]-a[2]*b[2],sub=(a,b)=>a.map((v,i)=>v-b[i]);
  const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],-(a[0]*b[1]-a[1]*b[0])];
  const toZ=X=>[X[0]/(1+X[2]),X[1]/(1+X[2])],px=z=>[C+z[0]*R,C-z[1]*R];
  side.innerHTML=`<div class="ch">Чертёжный стол Криволинейных</div><h4>Описание без циркуля</h4><p>Церковь учит: через любые три точки проходит окружность. Перетаскивайте вершины треугольника в круге Пуанкаре. Голубые линии — серединные перпендикуляры к сторонам; где они сходятся, там центр (курсовая, п. 3.5).</p>
  <ul class="tasks"><li data-t="circle">Окружность: перпендикуляры пересекаются внутри</li><li data-t="horo">Орицикл: перпендикуляры сходятся на абсолюте</li><li data-t="equi">Эквидистанта: перпендикуляры расходятся</li></ul><p class="st"></p><div class="row"><button class="btn" data-k="x">Отойти от стола</button></div>`;
  function iso(f,N,col,dash,lw){const h=2/N,v=[];for(let j=0;j<=N;j++){v.push([]);for(let i=0;i<=N;i++){const z=[-1+i*h,-1+j*h];v[j].push(z[0]*z[0]+z[1]*z[1]<0.997?f(toH(z)):NaN);}}
    x.strokeStyle=col;x.lineWidth=lw||3;x.setLineDash(dash||[]);x.beginPath();
    for(let j=0;j<N;j++)for(let i=0;i<N;i++){const a=v[j][i],b=v[j][i+1],c=v[j+1][i+1],d=v[j+1][i];if([a,b,c,d].some(Number.isNaN))continue;
      const pts=[];const e=(p,q,z1,z2)=>{if((p<0)!==(q<0)){const t=p/(p-q);pts.push([z1[0]+(z2[0]-z1[0])*t,z1[1]+(z2[1]-z1[1])*t]);}};
      const z00=[-1+i*h,-1+j*h],z10=[z00[0]+h,z00[1]],z11=[z00[0]+h,z00[1]+h],z01=[z00[0],z00[1]+h];
      e(a,b,z00,z10);e(b,c,z10,z11);e(c,d,z11,z01);e(d,a,z01,z00);
      for(let k=0;k+1<pts.length;k+=2){const p1=px(pts[k]),p2=px(pts[k+1]);x.moveTo(...p1);x.lineTo(...p2);}}
    x.stroke();x.setLineDash([]);}
  function draw(){const H=P.map(toH);boardBG(x,W);
    x.strokeStyle='#d6a35a';x.lineWidth=4;x.beginPath();x.arc(C,C,R,0,7);x.stroke();
    const n=[sub(H[0],H[1]),sub(H[1],H[2]),sub(H[2],H[0])];
    for(const m of n)iso(X=>ip(X,m),110,'rgba(120,200,255,.55)',[10,8],2.5);
    let c=cross(n[0],n[1]);const q=ip(c,c),rel=q/(c[0]*c[0]+c[1]*c[1]+c[2]*c[2]);
    const type=rel<-0.02?'circle':rel>0.02?'equi':'horo';
    if(prev&&prev!==type&&prev!=='horo'&&type!=='horo')found.horo=1; // прошли через орицикл по непрерывности
    found[type]=1;prev=type;
    const k=ip(H[0],c);iso(X=>ip(X,c)-k,160,type==='circle'?'#ffe2a0':type==='horo'?'#9fdc8a':'#ff9a80',null,4);
    if(type==='circle'){if(c[2]<0)c=c.map(v=>-v);const cz=toZ(c.map(v=>v/Math.sqrt(-q)));x.fillStyle='#ffe2a0';x.beginPath();x.arc(...px(cz),8,0,7);x.fill();}
    else if(type==='horo'){const cc=c[2]<0?c.map(v=>-v):c,z=[cc[0]/cc[2],cc[1]/cc[2]],l=Math.hypot(...z);x.fillStyle='#9fdc8a';x.beginPath();x.arc(...px([z[0]/l,z[1]/l]),10,0,7);x.fill();}
    else iso(X=>ip(X,c),130,'rgba(255,154,128,.7)',[4,6],2);
    // стороны треугольника — отрезки геодезических
    x.strokeStyle='#e8f1ff';x.lineWidth=3.5;
    for(let s2=0;s2<3;s2++){const A=H[s2],B=H[(s2+1)%3],d=Math.acosh(Math.max(1,-ip(A,B)));x.beginPath();
      for(let i=0;i<=40;i++){const t=i/40,X=A.map((v,j)=>(Math.sinh((1-t)*d)*v+Math.sinh(t*d)*B[j])/Math.sinh(d)),p=px(toZ(X));i?x.lineTo(...p):x.moveTo(...p);}x.stroke();}
    P.forEach((z,i)=>{x.fillStyle='#d6a35a';x.beginPath();x.arc(...px(z),13,0,7);x.fill();x.fillStyle='#0b1d36';x.font='600 18px IBM Plex Sans';x.textAlign='center';x.fillText('ABC'[i],...px(z).map((v,j)=>v+(j?6:0)));});
    const names={circle:'окружность — центр внутри круга',horo:'орицикл — центр на абсолюте',equi:'эквидистанта — у кривой нет центра, есть базовая прямая'};
    side.querySelectorAll('.tasks li').forEach(li=>li.classList.toggle('done',!!found[li.dataset.t]));
    const stt=side.querySelector('.st');stt.innerHTML=`Сейчас через A, B, C проходит <b>${names[type]}</b>.`+(Math.abs(rel)<0.08&&type!=='horo'?' Почти орицикл!':'');
    if(found.circle&&found.horo&&found.equi&&!done){done=true;stt.innerHTML+=`<br><b style="color:#9fdc8a">Пароль верный.</b> Не через любые три точки проходит окружность — и значит, пятый постулат здесь ложен.`;AU.pick();setTimeout(()=>close(true),2600);}}
  const zOf=e=>{const r=cv.getBoundingClientRect();return [((e.clientX-r.left)/r.width*W-C)/R,-((e.clientY-r.top)/r.height*W-C)/R];};
  cv.addEventListener('pointerdown',e=>{const z=zOf(e);let best=-1,bd=0.09;P.forEach((p2,i)=>{const d=Math.hypot(p2[0]-z[0],p2[1]-z[1]);if(d<bd){bd=d;best=i;}});drag=best;if(drag>=0)try{cv.setPointerCapture(e.pointerId);}catch(_){}});
  cv.addEventListener('pointermove',e=>{if(drag<0)return;let z=zOf(e);const l=Math.hypot(...z);if(l>0.93)z=z.map(v=>v*0.93/l);P[drag]=z;draw();});
  cv.addEventListener('pointerup',()=>drag=-1);
  side.addEventListener('click',e=>{if(e.target.closest('[data-k=x]'))close(false);});
  draw();}
// ═══════════════ рендер и HUD ═══════════════
function objects(){const out=[];
  for(const G of S.guards){const F=frameAt(G.pos,G.dir,S.A.kind==='plane'?[0,0,1,0]:null);const gr=S.A.lights?S.A.roomOf(G.pos):-1;
    out.push({pos:G.pos,F,kind:1,par:G.state==='chase'?1:G.alert*0.6,sl:G.sleep,walk:G.sleep?0:S.time-(G.mvT||-9)<0.2?(G.state==='chase'?2:1):0,vr:G.kassel?1:G.vr,lit:S.A.lights?(gr>=0&&S.lit[gr]):1,light:S.A.lights&&gr>=0?S.A.ROOMS[gr].c:advancePose(G.pos,S.A.up(G.pos),0.55).p});}
  if(LV.mirror){const M=LV.mirror(),G=S.guards[M.g];if(G&&!G.sleep){const p2=apply(M.R,G.pos),d2=apply(M.R,G.dir);
    out.push({pos:p2,F:frameAt(p2,d2),kind:S.lensOn?10:1,vr:S.lensOn?4:G.vr,par:0,lit:1,light:advancePose(p2,S.A.up(p2),0.55).p});}}
  if(S.decoy)out.push({pos:S.decoy.pos,F:S.decoy.F,kind:10,vr:4,lit:1,light:advancePose(S.decoy.pos,S.A.up(S.decoy.pos),0.5).p});
  for(const it of visibleItems()){const on=it.kind===5?(it.exit&&!it.exit(S)?0:1):it.kind===17?(S.flags[it.puzzle+'Done']?1:0):0;
    out.push({pos:it.pos,F:it.F,dirE:it.dirE,kind:it.kind,par:it.par??on,vr:it.vr||0,lit:S.A.lights?(it.room>=0&&S.lit[it.room]):1,light:it.light});}
  return out;}
function mapMarks(){return LV&&LV.marks?LV.marks(S):[];}
const EXPO={prologue:0.5,ch1:1,ch2:0.62,ch3:0.55,ch4:0.62,ch5:0.7};
function render(now){const SC=sceneBegin();let ob=objects();if(ob.length>16){const p=S.A.pos();ob=ob.map(o=>({o,d:S.A.dist(p,o.pos)})).sort((a,b)=>a.d-b.d).slice(0,16).map(x=>x.o);}S.A.render(SC,now,ob);if(typeof POST!=='undefined')POST.cfg.expo=EXPO[CH().id]??1;sceneEnd(SC,now);}
const ui={obj(){const L=$('mlist');if(!L||!S)return;$('mchap').textContent=CH().n+' · '+CH().title;
    L.innerHTML=LV.objectives(S).map(o=>`<li class="${o.done?'done':o.locked?'locked':''}">${o.t}</li>`).join('');
    $('ab-blink').style.display=S.abil.blink?'':'none';$('ab-lens').classList.toggle('off',!S.abil.lens);$('ab-decoy').classList.toggle('off',!S.abil.decoy);}};
function hud(){
  $('mmana').textContent=fmt(S.mana);$('mfill').style.width=(S.mana*100).toFixed(1)+'%';
  $('mclar').textContent=fmt(S.clar);$('mcfill').style.width=(S.clar*100).toFixed(1)+'%';$('mclar').parentNode.style.display=$('mcfill').parentNode.style.display=S.abil.lens?'':'none';
  const t=S.over||S.paused||S.dlg?null:interactTarget();const pe=$('mprompt');
  if(t){pe.innerHTML=t.type==='none'?t.label:`<b>[F]</b> ${t.label}`;pe.style.display='block';}else pe.style.display='none';
  $('mlensv').style.opacity=S.lensOn?1:0;
  document.getElementById('danger').style.opacity=(S.over?0:Math.min(1,S.maxA||0)*0.85).toFixed(3);
  if(toastT&&performance.now()>toastT){$('mtoast').style.opacity=0;toastT=0;}
  AU.setDrone(S.maxA||0,!S.over&&!S.paused);
  const box=$('mind');while(box.children.length<S.guards.length){const e=document.createElement('div');e.className='gi';e.innerHTML='<i></i>';box.appendChild(e);}
  for(let i=S.guards.length;i<box.children.length;i++)box.children[i].style.display='none';
  if(S.A.kind!=='flat'){const p=S.A.pos(),b=[0,1,2].map(k=>S.A.basis(k)),tf=fovTan(),W=innerWidth,H=innerHeight;
    S.guards.forEach((G,i)=>{const e=box.children[i];
      if(G.sleep||S.over||S.dlg||(G.alert<0.04&&G.state!=='chase')){e.style.display='none';return;}
      const d=hyperbolicDistance(p,G.pos),dir=dirTo(p,G.pos),x=md(dir,b[0]),y=md(dir,b[1]),z=md(dir,b[2]);
      if(z<0.05){e.style.display='none';return;}
      const ar=Math.asin(clamp(Math.sinh(0.13)/Math.sinh(Math.max(d,0.15)),0,1));
      e.style.display='block';e.style.left=(W/2+(x/z)/tf*H/2)+'px';e.style.top=(H/2-(y/z)/tf*H/2-Math.tan(ar)/tf*H/2-8)+'px';
      e.className='gi'+(G.state==='chase'?' chase':'')+(G.kassel?' k':'');e.firstChild.style.height=(G.state==='chase'?100:G.alert*100).toFixed(0)+'%';});}
  if(S.A.kind==='plane'&&!S.over){const P=2*Math.atan(Math.exp(-S.c.h));$('mroom').textContent='h = '+fmt(S.c.h)+' · Π(h) = '+fmt(P*180/Math.PI,1)+'°';}
  lectHUD();drawKlein();
  if(mapOn)drawMap();
}
// Линза: всё пространство как шар Кэли — Клейна в системе камеры. Прямые — хорды, абсолют — окружность,
// полюсы стен текущей комнаты — за абсолютом. Проекция ортогональная: шар виден «спереди».
function drawKlein(){const on=S.lensOn&&!S.over&&!S.dlg&&S.A.kind!=='flat';kleinC.style.opacity=on?1:0;if(!on)return;
  const W=kleinC.width=innerWidth*Math.min(devicePixelRatio||1,1.5),H=kleinC.height=innerHeight*Math.min(devicePixelRatio||1,1.5),x=kleinC.getContext('2d');
  const A=S.A,p=A.pos(),b=[0,1,2].map(k=>A.basis(k)),Rk=Math.min(W,H)*0.40,cx=W/2,cy=H/2;
  const K=X=>{const w=-md(X,p);return [md(X,b[0])/w,md(X,b[1])/w];},sc=k=>[cx+k[0]*Rk,cy-k[1]*Rk];
  x.lineCap='round';
  x.strokeStyle='rgba(240,205,140,.85)';x.lineWidth=2.2;x.beginPath();x.arc(cx,cy,Rk,0,7);x.stroke();
  x.fillStyle='rgba(240,205,140,.75)';x.font=`${Math.round(Rk*0.05)}px IBM Plex Sans, sans-serif`;x.textAlign='center';x.fillText('абсолют',cx,cy-Rk-10);
  if(A.kind==='rooms'){const cur=S.room;
    A.ROOMS.forEach((r,i)=>{const vs=A.roomVerts(i).map(K);x.strokeStyle=i===cur?'rgba(200,235,255,.9)':'rgba(150,205,255,.32)';x.lineWidth=i===cur?1.8:1;x.beginPath();
      for(const [a,c] of A.EDGES){x.moveTo(...sc(vs[a]));x.lineTo(...sc(vs[c]));}x.stroke();});
    if(cur>=0){A.roomFaces(cur).forEach((n,k)=>{const w=-md(n,p);if(Math.abs(w)<1e-6)return;const q=[md(n,b[0])/w,md(n,b[1])/w],l=Math.hypot(...q);if(l<1)return;
      const lim=Math.min(W,H)*0.49/Rk,qq=l>lim?q.map(v=>v*lim/l):q,P=sc(qq);x.fillStyle='rgba(255,226,160,.9)';x.beginPath();x.arc(...P,4,0,7);x.fill();
      if(k===0){x.fillText('полюс стены',P[0],P[1]-10);}});}}
  if(A.kind==='house'){const c=S.c,f=2**c.L,cx0=Math.floor(c.X),cy0=Math.floor(c.Y),W0=K([0,0,1,1]);
    x.strokeStyle='rgba(200,235,255,.55)';x.lineWidth=1.2;x.beginPath();
    for(let i=cx0-2;i<=cx0+3;i++)for(let j=cy0-2;j<=cy0+3;j++){const X0=i*f,Y0=j*f,r2=X0*X0+Y0*Y0,n=[2*X0,2*Y0,r2-1,r2+1];x.moveTo(...sc(K(n)));x.lineTo(...sc(W0));}
    x.stroke();const Pw=sc(W0);x.fillStyle='rgba(255,226,160,.95)';x.beginPath();x.arc(...Pw,6,0,7);x.fill();x.fillText('ω — общий конец параллельных',Pw[0],Pw[1]-12);}
  if(campaign.defectSight){for(const it of visibleItems()){if(it.kind===7||it.kind===9){const P=sc(K(it.pos)),g=x.createRadialGradient(...P,0,...P,it.kind===9?40:18);
    g.addColorStop(0,it.kind===9?'rgba(255,250,235,.9)':'rgba(190,120,255,.9)');g.addColorStop(1,'rgba(150,80,255,0)');x.fillStyle=g;x.beginPath();x.arc(...P,it.kind===9?40:18,0,7);x.fill();}}
    x.fillStyle='rgba(190,140,255,.8)';x.fillText('дефект',cx,cy+Rk+20);}
  // спящий орицикл: окружность Пуанкаре, касающаяся абсолюта, перенесённая в модель Клейна
  x.strokeStyle='rgba(159,220,138,.75)';x.lineWidth=1.6;x.beginPath();const t0=3.8,rh=0.32;
  for(let i=0;i<=80;i++){const a=i/80*Math.PI*2,z=[(1-rh)*Math.cos(t0)+rh*Math.cos(a),(1-rh)*Math.sin(t0)+rh*Math.sin(a)],r2=z[0]*z[0]+z[1]*z[1],kq=[2*z[0]/(1+r2),2*z[1]/(1+r2)],P=sc(kq);i?x.lineTo(...P):x.moveTo(...P);}x.stroke();
  x.fillStyle='rgba(159,220,138,.85)';x.fillText('орицикл',...sc([0.62*Math.cos(t0),0.62*Math.sin(t0)]));
  for(const G of S.guards){if(G.sleep)continue;const P=sc(K(G.pos));x.fillStyle='rgba(255,90,60,.9)';x.beginPath();x.arc(...P,5,0,7);x.fill();}
  for(const it of visibleItems()){if(it.kind===2||it.kind===3||it.kind===4){const P=sc(K(it.pos));x.fillStyle='rgba(255,215,120,.85)';x.beginPath();x.arc(...P,3,0,7);x.fill();}}}
function lectHUD(){const e=$('mlect');if(!campaign.lecturer||S.over){e.style.display='none';return;}
  const A=S.A,p=A.pos(),card=(STORY.cards||[]).find(c=>c.ch===CH().id)||{};const rows=[];
  rows.push(['до старта',fmt(A.dist(p,S.start))]);
  if(A.kind==='rooms'){rows.push(['переходов через грани',String(S.c.cross)]);rows.push(['многогранников у ребра',CH().id==='ch5'?'5 (угол 72°)':'4 (угол 90°)']);}
  if(A.kind==='house'){rows.push(['этаж',String(S.c.L)]);rows.push(['масштаб этажа',String(2**S.c.L)+'×']);rows.push(['высота над полом',fmt(S.c.h)+' из ln 2 ≈ 0,69']);}
  if(A.kind==='plane'){const P=2*Math.atan(Math.exp(-S.c.h));rows.push(['высота h',fmt(S.c.h)]);rows.push(['Π(h)',fmt(P*180/Math.PI,1)+'°']);}
  if(A.kind==='flat')rows.push(['сумма углов грани','360°']);
  e.innerHTML=`<h5>Режим «Лектор» · стражи не видят</h5><div class="th">${card.theorem||''}</div>`+rows.map(([k,v])=>`<div class="rw"><span>${k}</span><span>${v}</span></div>`).join('');e.style.display='block';}
function drawMap(){const x=mapC.getContext('2d'),W=mapC.width,R=W*0.46;x.clearRect(0,0,W,W);
  const A=S.A;x.font='500 26px IBM Plex Sans, sans-serif';x.textAlign='center';x.fillStyle='rgba(236,229,214,.6)';
  if(!A.ROOMS){x.fillText(A.kind==='plane'?'Карта — справа внизу':'Планшет здесь не работает',W/2,W/2);return;}
  const pr=k=>{const a=k[0]/k[3],b=k[1]/k[3],cc=k[2]/k[3];return [W/2+R*(0.82*a-0.5*cc),W/2-R*(0.85*b+0.28*a+0.25*cc)];};
  x.lineWidth=3;x.strokeStyle='rgba(214,163,90,.55)';const R_=A.ROOMS;
  for(const i of S.visited)for(const j of R_[i].nb)if(S.visited.includes(j)&&i<j){const a=pr(R_[i].c),b=pr(R_[j].c);x.beginPath();x.moveTo(...a);x.lineTo(...b);x.stroke();}
  const known=new Set(S.visited.filter(i=>i>=0&&i<R_.length));for(const i of [...known])for(const j of R_[i].nb)known.add(j);
  for(const i of known){const [X,Y]=pr(R_[i].c),v=S.visited.includes(i);
    x.fillStyle=v?(S.lit[i]?'#d6a35a':'#3b4a6b'):'rgba(120,130,160,.35)';x.beginPath();x.arc(X,Y,v?14:9,0,7);x.fill();
    x.fillStyle=v?'#ece5d6':'rgba(236,229,214,.4)';x.fillText(v?R_[i].name:'?',X,Y-24);}
  const [PX,PY]=pr(A.pos());x.fillStyle='#ff5a3a';x.beginPath();x.arc(PX,PY,10,0,7);x.fill();
  x.fillStyle='rgba(236,229,214,.6)';x.font='22px IBM Plex Sans, sans-serif';x.fillText('Планшет: модель Кэли — Клейна, косая проекция',W/2,W-60);}

// ═══════════════ экраны ═══════════════
function screenShow(html){const e=screen;e.innerHTML=`<div class="card framed">${html}</div>`;e.classList.add('on');
  try{if(document.pointerLockElement)document.exitPointerLock();}catch(_){}
  e.querySelectorAll('[data-a]').forEach(b=>b.addEventListener('click',()=>act(b.dataset.a,b.dataset)));
  const m=e.querySelector('.btn.main');if(m)m.focus({preventScroll:true});e.querySelector('.card').scrollTop=0;}
function screenHide(){screen.classList.remove('on');screen.innerHTML='';}
let lockReqT=0;
function lock(){if(matchMedia('(pointer:coarse)').matches||!active||document.pointerLockElement===canvas)return;lockReqT=performance.now();try{const r=canvas.requestPointerLock();if(r&&r.catch)r.catch(()=>{});}catch(_){}}
function controlsHTML(ch){const c=CHS[ch];const fl=c.engine==='flat';
  return `<div class="ctrls"><b>W A S D</b><span>${c.engine==='plane'?'идти по равнине':c.engine==='house'?'идти по этажу':'идти (пространство без «низа»)'}; Пробел и C — вверх и вниз</span><b>Shift</b><span>бежать${fl?'':' — громко, стражи слышат'}</span>
  ${fl?'':`<b>ПКМ (держать)</b><span>геодезический рывок: прицел, отпустить — переместиться</span><b>V</b><span>Линза Абсолюта: стражи и их взгляд сквозь стены</span><b>G (держать)</b><span>зеркало σ — отражение, которое уводит стражей</span>`}
  <b>F</b><span>${fl?'снять показания, взять предмет':'усыпить стража со спины, взять предмет, погасить лампу'}</span>${c.engine==='rooms'?'<b>Tab</b><span>планшет-карта</span>':''}<b>K / L</b><span>сохранить / загрузить</span><b>Esc</b><span>пауза</span></div>`;}
function title(){
  const cur=Math.min(campaign.unlocked,CHS.length-1);
  screenShow(`<div class="crest">${emblemSVG()}<div class="wordmark">${FONT.svg('Пятый Постулат',{h:'58px',weight:1.35})}</div><div class="ch">игра о геометрии Лобачевского</div></div>
  <p style="text-align:center">В городе, где Церковь Евклида силой удерживает пространство плоским, архитектор-чертёжница получает Линзу Абсолюта — и видит, что весь мир построен на лжи.</p>
  <div class="row" style="text-align:center">${campaign.unlocked>0||hasSave()?`<button class="btn main" data-a="continue_c">Продолжить${hasSave()?'':': '+CHS[cur].n}</button>`:''}<button class="btn${campaign.unlocked>0||hasSave()?'':' main'}" data-a="new">Новая игра</button>
  <button class="btn" data-a="chapters">Главы</button><button class="btn" data-a="lemmas">Леммы</button><button class="btn" data-a="records">Записи вычеркнутых</button><button class="btn" data-a="glossary">Глоссарий</button><button class="btn" data-a="gallery">Портретная галерея</button><button class="btn" data-a="history">Как было на самом деле</button><button class="btn" data-a="teacher">Для учителя${campaign.lecturer?' · Лектор':''}</button><button class="btn" data-a="quit">Прогулка по мирам</button></div>`);}
function backBtn(){return `<div class="row"><button class="btn" data-a="${S&&!S.over&&active&&S.time>0?'resume':'title'}">Назад</button></div>`;}
function records(){const R=STORY.records,ids=Object.keys(R),got=ids.filter(k=>(campaign.records||{})[k]);
  screenShow(`<div class="ch">Изъято Церковью</div><h2>Записи вычеркнутых · ${got.length} из ${ids.length}</h2><p>Листы переписи, которые Собор приказал уничтожить. Лист 281 — в Архиве; остальные разбросаны по Городу.</p>${got.length?got.map(k=>`<div class="card2"><b style="font-family:var(--display);font-size:19px;font-weight:400;color:var(--brass)">${R[k].t}</b><p>${R[k].x}</p></div>`).join(''):'<p>Пока ни одной. Ищите белые листы с сургучом.</p>'}${backBtn()}`);}
function glossary(){screenShow(`<div class="ch">Справочник</div><h2>Глоссарий</h2>${STORY.glossary.map(g=>`<div class="gl"><b>${g.t}</b>${g.ref?`<small>курсовая, ${g.ref}</small>`:''}<p>${g.d}</p></div>`).join('')}${backBtn()}`);}
function historyScr(){screenShow(`<div class="ch">Историческая справка</div><h2>Как было на самом деле</h2><p>Игра — вымысел, но леммы, даты и цитаты в ней настоящие. Вот где вымысел, а где история.</p>${STORY.history.map(h=>`<div class="card2"><p><i>В игре:</i> ${h.f}</p><p><b>На самом деле:</b> ${h.h}</p></div>`).join('')}${backBtn()}`);}
function teacher(){screenShow(`<div class="ch">Педагогический слой</div><h2>Для учителя</h2>
  <p>Режим «Лектор» отключает стелс (стражи не замечают игрока) и выводит на экран теорему главы и живые измерения — расстояние до старта, этаж и масштаб, Π(h). Удобно показывать на уроке через проектор.</p>
  <div class="row"><button class="btn main" data-a="lect">Режим «Лектор»: ${campaign.lecturer?'включён':'выключен'}</button><button class="btn" data-a="print">Распечатать карточки</button></div>
  <h3 style="font:600 11px var(--body);letter-spacing:.16em;text-transform:uppercase;color:var(--brass);margin-top:16px">Методические карточки</h3>
  ${STORY.cards.map(c=>{const ch=CHS.find(x=>x.id===c.ch);return `<div class="card2"><h4>${ch.n}. ${ch.title}</h4><p><b>Цель:</b> ${c.goal}</p><p><b>Теорема:</b> ${c.theorem}</p><p><b>Что наблюдать:</b> ${c.observe}</p><p><b>Вопросы для обсуждения:</b></p><ul>${c.questions.map(q=>`<li>${q}</li>`).join('')}</ul><p><b>Связь с курсовой:</b> ${c.ref||'—'}.${c.scenes?` <b>Сцены «Круга Кэли — Клейна»:</b> ${c.scenes}.`:''} <b>Мир для самостоятельной прогулки:</b> ${c.world}.</p></div>`;}).join('')}
  ${backBtn()}`);}
function chapters(){screenShow(`<div class="ch">Пятый Постулат</div><h2>Главы</h2><div class="chlist">${CHS.map((c,i)=>`<button data-a="brief" data-ch="${i}" ${i>campaign.unlocked?'disabled':''}><span>${c.title}</span><small>${c.n}</small></button>`).join('')}</div>
  <div class="row"><button class="btn" data-a="title">Назад</button></div>`);}
function lemmas(){const ids=Object.keys(STORY.lemmas);const got=ids.filter(k=>campaign.lemmas[k]);
  screenShow(`<div class="ch">Журнал</div><h2>Леммы · ${got.length} из ${ids.length}</h2>
  ${got.length?got.map(k=>{const L=STORY.lemmas[k],P=PORTRAITS.info(L.by);return `<div class="lem">${PORTRAITS.svg(L.by,'portrait')}<div><b>${L.t}</b><div style="font-size:11px;color:var(--muted)">${P.name} · ${P.sub}</div><p>${L.x}</p>${STORY.proofs&&STORY.proofs[k]?`<details><summary>Доказательство в строку</summary><p>${STORY.proofs[k]}</p></details>`:''}</div></div>`;}).join(''):'<p>Пока ни одной. Леммы — золотые точки, чаще всего в тёмных комнатах.</p>'}
  <div class="row"><button class="btn" data-a="${S&&!S.over&&active&&S.time>0?'resume':'title'}">Назад</button></div>`);}
function gallery(){const P=PORTRAITS.list;const hist=new Set(Object.values(STORY.lemmas).filter((_,i)=>true).map(l=>l.by));
  const owned=new Set(Object.keys(campaign.lemmas).map(k=>STORY.lemmas[k].by));
  const cast=['vera','nikolai','ortt','kassel','oricycla','bernhard','euclid','guard'];
  screenShow(`<div class="ch">Бронзированные силуэты</div><h2>Портретная галерея</h2>
  <p>Силуэтный профиль был любимым портретным жанром 1820–1840-х — эпохи Лобачевского, Бойяи и Гаусса. Силуэты стилизованы по мотивам известных портретов; где подлинного изображения нет, это отмечено. Исторические портреты открываются вместе с их леммами.</p>
  <h3 style="font:600 11px var(--body);letter-spacing:.16em;text-transform:uppercase;color:var(--brass)">Действующие лица</h3>
  <div class="gallery">${cast.map(id=>`<figure>${PORTRAITS.svg(id,'')}<figcaption><b>${P[id].name}</b><span>${P[id].sub}</span></figcaption></figure>`).join('')}</div>
  <h3 style="font:600 11px var(--body);letter-spacing:.16em;text-transform:uppercase;color:var(--brass)">Геометры</h3>
  <div class="gallery">${[...hist].map(id=>{const o=owned.has(id);return `<figure class="${o?'':'lock'}">${PORTRAITS.svg(id,'')}<figcaption><b>${o?P[id].name:'???'}</b><span>${o?P[id].sub:'найдите лемму'}</span>${o&&P[id].cond?`<span style="display:block;font-size:11px;font-style:italic">${P[id].cond}</span>`:''}</figcaption></figure>`;}).join('')}</div>
  <div class="row"><button class="btn" data-a="title">Назад</button></div>`);}
function brief(i){const c=CHS[i];
  screenShow(`<div class="crest">${i===0?emblemSVG():''}<span class="fxl">${FONT.svg(c.n,{h:'30px'})}</span><h2>${c.title}</h2></div>${c.brief.map(x=>`<p>${x}</p>`).join('')}
  <div class="q">${c.quote}</div>${controlsHTML(i)}
  <div class="row"><button class="btn main" data-a="start" data-ch="${i}">Начать</button><button class="btn" data-a="title">В меню</button></div>`);}
function pause(){if(!S||S.over||S.dlg)return;S.paused=true;aiming=false;
  screenShow(`<div class="ch">Пауза · ${CH().n}</div><h2>${CH().title}</h2>
  <div class="row"><button class="btn main" data-a="resume">Продолжить</button><button class="btn" data-a="save">Сохранить <span class="mono">(K)</span></button>
  ${hasSave()?'<button class="btn" data-a="load">Загрузить <span class="mono">(L)</span></button>':''}<button class="btn" data-a="restart">Заново</button><button class="btn" data-a="lemmas">Леммы</button><button class="btn" data-a="records">Записи</button><button class="btn" data-a="sound">Звук: ${AU.on?'вкл':'выкл'}</button><button class="btn" data-a="menu">В меню</button></div>
  ${controlsHTML(S.ch)}`);}
function start(i){S=fresh(i);LV.start&&LV.start();const go=()=>{begin();say('start');};const cs=()=>{if(CH().cutscene){screenHide();scene(CH().cutscene,go);}else go();};if(CH().intro)intro(CH().intro,cs);else cs();}
// П0.1–П0.2: чёрный экран, луч чертит квадрат, один угол «плывёт» на градус; титульные карточки
function intro(cards,cb){const e=document.createElement('div');e.id='mintro';
  e.innerHTML=`<svg viewBox="0 0 200 200"><path id="isq" d="M50 50H150V150H50Z" fill="none" stroke="#f3ead6" stroke-width="1.6" stroke-linecap="square"/></svg><div class="cap"></div><div class="skip">Пробел — пропустить</div>`;
  document.body.appendChild(e);const sq=e.querySelector('#isq'),cap=e.querySelector('.cap');let done=false,ts=[];
  const fin=()=>{if(done)return;done=true;ts.forEach(clearTimeout);removeEventListener('keydown',kd,true);e.classList.add('out');setTimeout(()=>e.remove(),600);cb();};
  const kd=ev=>{if(ev.code==='Space'||ev.code==='Escape'||ev.code==='Enter'){ev.preventDefault();ev.stopPropagation();fin();}};
  addEventListener('keydown',kd,true);e.addEventListener('click',fin);
  ts.push(setTimeout(()=>{sq.setAttribute('d','M50 50H150V150L50.9 151.7Z');AU.tone(440,0.5,'sine',0.05);AU.tone(452,0.5,'sine',0.04);},3400));
  ts.push(setTimeout(()=>e.querySelector('svg').classList.add('gone'),4600));
  cards.forEach((c,k)=>{ts.push(setTimeout(()=>{cap.classList.remove('on');setTimeout(()=>{cap.textContent=c;cap.classList.add('on');},350);},k===0?400:5200+(k-1)*2600));});
  ts.push(setTimeout(fin,5200+(cards.length-1)*2600+1800));}
function act(a,ds){AU.init();
  if(a==='new'){campaign={unlocked:0,lemmas:campaign.lemmas,alerts:0,sleeps:0,bodies:0,decoy:0,met:{},endings:campaign.endings};saveCampaign();brief(0);}
  else if(a==='continue_c'){if(hasSave()&&load())begin();else brief(Math.min(campaign.unlocked,CHS.length-1));}
  else if(a==='chapters')chapters();
  else if(a==='lemmas')lemmas();
  else if(a==='gallery')gallery();
  else if(a==='title'||a==='menu'){if(S)S.paused=true;title();}
  else if(a==='brief')brief(+ds.ch);
  else if(a==='start')start(+ds.ch);
  else if(a==='next')brief(S.ch+1);
  else if(a==='restart')brief(S.ch);
  else if(a==='resume'){S.paused=false;screenHide();lock();}
  else if(a==='load'){if(load())begin();}
  else if(a==='save')save();
  else if(a==='sound'){AU.on=!AU.on;pause();}
  else if(a==='quit')exit();
  else if(a==='check'){const ck=STORY.checks[CH().id],ok=+ds.i===ck.ok,e=screen.querySelector('.ce');e.hidden=false;e.innerHTML=(ok?'<b style="color:#9fdc8a">Верно.</b> ':'<b style="color:#ff8a6a">Не совсем.</b> ')+ck.e;
    screen.querySelectorAll('[data-a=check]').forEach(b=>{b.disabled=true;if(+b.dataset.i===ck.ok)b.classList.add('main');});if(ok){campaign.checks={...(campaign.checks||{}),[CH().id]:1};saveCampaign();}}
  else if(a==='glossary')glossary();
  else if(a==='records')records();
  else if(a==='history')historyScr();
  else if(a==='teacher')teacher();
  else if(a==='lect'){campaign.lecturer=!campaign.lecturer;saveCampaign();teacher();}
  else if(a==='print'){window.print();}}
function begin(){document.body.classList.add('p5play');touchReset();if(matchMedia('(pointer:coarse)').matches&&!document.fullscreenElement)goFull();S.paused=false;S.over=false;S.room=-1;$('mroom').textContent='';screenHide();ui.obj();$('mplaque').style.display='none';$('msub').style.opacity=0;
  document.getElementById('mapwrap').hidden=S.A.kind!=='plane';document.getElementById('mapwrap').style.visibility=S.A.kind==='plane'?'visible':'hidden';lock();}
function open(){const bad=['rooms','house','plane','flat'].filter(k=>!PROG[k]);if(bad.length){alert('Шейдеры не собрались: '+bad.join(', ')+'\n'+(PROG[bad[0]+'_err']||'').toString().slice(0,400));return;}
  active=true;document.body.classList.add('mission');hudEl.classList.add('on');
  for(const id of ['top','panel','stats','hint','mapwrap'])$(id).style.visibility='hidden';
  title();}
function exit(){active=false;aiming=false;mapOn=false;mapC.classList.remove('on');screenHide();dlg.classList.remove('on');hudEl.classList.remove('on');document.body.classList.remove('mission','p5play');
  for(const id of ['top','panel','stats','hint','mapwrap'])$(id).style.visibility='';
  document.getElementById('danger').style.opacity=0;AU.setDrone(0,false);if(S)S.paused=true;setWorld(world);
  try{if(document.pointerLockElement)document.exitPointerLock();}catch(_){}}

// ───────── ввод ─────────
function key(e,down){if(!active)return false;const k=e.code;
  if(S&&S.dlg){if(tbl.classList.contains('on')){if(down&&k==='Escape'){tbl.querySelector('[data-k=x]')?.click();}return true;}
    if(down&&(k==='Space'||k==='Enter'||k==='KeyF')&&dlg._next){e.preventDefault();dlg._next();}return true;}
  if(screen.classList.contains('on')||!S)return /^(Digit\d|KeyR|KeyH)$/.test(k);
  if(!down){if(k==='Tab'){mapOn=false;mapC.classList.remove('on');}
    if(k==='KeyB'&&aiming&&aimMode==='blink'){aiming=false;doBlink();}if(k==='KeyG'&&aiming&&aimMode==='decoy'){aiming=false;doDecoy();}return false;}
  if(k==='Tab'){e.preventDefault();mapOn=true;mapC.classList.add('on');return true;}
  if(k==='KeyF'){interact();return true;}
  if(k==='KeyV'){toggleLens();return true;}
  if(k==='KeyB'){if(!e.repeat&&S.abil.blink){aiming=true;aimMode='blink';}return true;}
  if(k==='KeyG'){if(!e.repeat){if(S.abil.decoy){aiming=true;aimMode='decoy';}else toast('Зеркала σ ещё нет');}return true;}
  if(k==='KeyK'){save();return true;}
  if(k==='KeyL'){if(hasSave()&&load())begin();return true;}
  if(k==='Escape'||k==='KeyP'){pause();return true;}
  if(/^(Digit\d|KeyR|KeyH)$/.test(k))return true;
  return false;}
canvas.addEventListener('contextmenu',e=>{if(active)e.preventDefault();});
canvas.addEventListener('mousedown',e=>{if(active&&e.button===2&&S&&!S.paused&&!S.over&&S.abil.blink){aiming=true;aimMode='blink';}});
addEventListener('mouseup',e=>{if(active&&e.button===2&&aiming&&aimMode==='blink'){aiming=false;if(!S.paused&&!S.over)doBlink();}});
document.addEventListener('pointerlockchange',()=>{if(performance.now()-lockReqT<900)return;if(active&&!document.pointerLockElement&&S&&!S.paused&&!S.over&&!S.dlg&&!tbl.classList.contains('on'))pause();});
const tb=$('mt-blink');tb.addEventListener('pointerdown',e=>{aiming=true;aimMode='blink';tb.setPointerCapture(e.pointerId);});
tb.addEventListener('pointerup',()=>{if(aiming){aiming=false;doBlink();}});tb.addEventListener('pointercancel',()=>aiming=false);
const td=$('mt-decoy');td.addEventListener('pointerdown',e=>{aiming=true;aimMode='decoy';td.setPointerCapture(e.pointerId);});
td.addEventListener('pointerup',()=>{if(aiming){aiming=false;doDecoy();}});td.addEventListener('pointercancel',()=>aiming=false);
$('mt-lens').addEventListener('click',()=>toggleLens());
$('mt-act').addEventListener('click',interact);$('mpause').addEventListener('click',pause);
$('mprompt').addEventListener('click',()=>{if(S&&!S.dlg&&!S.paused)interact();});
const tgl=(id,code)=>{const b=$(id);b.addEventListener('click',()=>{const on=!keys.has(code);on?keys.add(code):keys.delete(code);b.classList.toggle('on',on);});};
tgl('mt-run','ShiftLeft');tgl('mt-crouch','ControlLeft');
$('mt-map').addEventListener('click',()=>{if(!S||screen.classList.contains('on'))return;mapOn=!mapOn;mapC.classList.toggle('on',mapOn);$('mt-map').classList.toggle('on',mapOn);});
$('mrot-x').addEventListener('click',()=>document.body.classList.add('p5rotok'));
function touchReset(){for(const c of ['ShiftLeft','ControlLeft'])keys.delete(c);for(const id of ['mt-run','mt-crouch','mt-map'])$(id).classList.remove('on');mapOn=false;mapC.classList.remove('on');
  $('mt-crouch').style.display=S&&(CH().id==='prologue'||CH().id==='ch4')?'block':'none';}
function goFull(){const d=document.documentElement;try{const r=(d.requestFullscreen||d.webkitRequestFullscreen||(()=>{})).call(d,{navigationUI:'hide'});
  const lk=()=>{try{screen.orientation&&screen.orientation.lock&&screen.orientation.lock('landscape').catch(()=>{});}catch(_){}};if(r&&r.then)r.then(lk).catch(()=>{});else lk();}catch(_){}}


function frame(dt,now){
  if(S&&!S.paused&&!S.over&&!S.dlg)update(dt);else look=[0,0];
  if(S)render(now);
  if(S&&now-(frame.h||0)>60){frame.h=now;hud();}
}
{const b=document.createElement('button');b.innerHTML='<kbd>7</kbd>Пятый Постулат';b.style.borderColor='var(--brass)';b.addEventListener('click',open);worldsEl.appendChild(b);}
addEventListener('keydown',e=>{if(!active&&e.code==='Digit7'&&!(e.target.tagName==='INPUT'))open();});
if(location.hash==='#archive'||location.hash==='#game')setTimeout(open,0);

return {get active(){return active;},frame,key,open,exit,
  _:{LEVELS,get S(){return S;},set S(v){S=v;},fresh,update,start,act,campaign:()=>campaign,PROG,frameAt,aimTarget,objects,interactTarget,interact,debate,startEscape,openTable}};
})();
window.MISSION=GAME;window.GAME=GAME;
