'use strict';
// ═══════════════ Полигональный рендер комнат ═══════════════
// В проективной модели Кэли — Клейна прямые остаются прямыми, а плоскости — плоскими, поэтому комнату-многогранник
// можно задать евклидовой сеткой в координатах Клейна и отдать видеокарте однородные координаты точки гиперболоида:
// обычная перспектива и буфер глубины работают точно. Материалы стен — те же, что у лучевого рендера (WALLS):
// точка складывается отражениями в фундаментальную область комнаты.
// Персонажи и предметы пока рисуются прежней формулой (SDF), но только внутри своего контура на экране.
function makeRaster(D){
const gl=D.gl,{mul,apply,linv,md,det4}=D;
const dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2],sub=(a,b)=>[a[0]-b[0],a[1]-b[1],a[2]-b[2]],add=(a,b)=>[a[0]+b[0],a[1]+b[1],a[2]+b[2]],sc=(a,s)=>[a[0]*s,a[1]*s,a[2]*s];
const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],nrm=a=>sc(a,1/(Math.hypot(...a)||1));
const NR=16,NG=8;
function compile(vs,fs){const mk=(t,s)=>{const sh=gl.createShader(t);gl.shaderSource(sh,s);gl.compileShader(sh);
    if(!gl.getShaderParameter(sh,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(sh));return sh;};
  const pr=gl.createProgram();gl.attachShader(pr,mk(gl.VERTEX_SHADER,vs));gl.attachShader(pr,mk(gl.FRAGMENT_SHADER,fs));
  gl.bindAttribLocation(pr,0,'aPos');gl.bindAttribLocation(pr,1,'aNrm');gl.bindAttribLocation(pr,2,'aTex');gl.bindAttribLocation(pr,3,'aRoom');
  gl.linkProgram(pr);if(!gl.getProgramParameter(pr,gl.LINK_STATUS))throw new Error(gl.getProgramInfoLog(pr));
  const loc={};const n=gl.getProgramParameter(pr,gl.ACTIVE_UNIFORMS);
  for(let i=0;i<n;i++){const u=gl.getActiveUniform(pr,i);loc[u.name.replace(/\[0\]$/,'')]=gl.getUniformLocation(pr,u.name);}
  return {pr,loc};}

// ───────── шейдеры комнат ─────────
const VS_ROOM=`#version 300 es
in vec3 aPos; in vec3 aNrm; in vec3 aTex; in float aRoom;
uniform mat4 uRoom[${NR}]; uniform mat4 uVM; uniform mat4 uPM;
out vec4 vXw; out vec4 vXl; out vec4 vNl; out vec3 vTex; flat out float vRoom;
void main(){
  vec4 X=vec4(aPos,1.)/sqrt(1.-dot(aPos,aPos));
  vec4 Pl=vec4(aNrm,dot(aNrm,aPos)); Pl/=sqrt(max(dot(aNrm,aNrm)-Pl.w*Pl.w,1e-6));
  int r=int(aRoom+.5);
  vXl=X; vNl=Pl; vXw=uRoom[r]*X; vTex=aTex; vRoom=aRoom;
  vec4 c=uVM*vXw; gl_Position=uPM*vec4(c.xy,-c.z,c.w);
}`;
const FS_ROOM=D.HEAD+`
in vec4 vXw; in vec4 vXl; in vec4 vNl; in vec3 vTex; flat in float vRoom;
uniform vec4 uM[4]; uniform vec4 uE1; uniform vec4 uE2;
uniform int uPal; uniform vec3 uLampC; uniform float uStraight; uniform float uTime; uniform float uLens;
uniform vec4 uCamW; uniform vec4 uCamL[${NR}]; uniform float uLit[${NR}]; uniform vec4 uRoomC[${NR}];
uniform vec4 uG[${NG}]; uniform vec4 uGD[${NG}]; uniform int uNG; uniform float uCosFov; uniform float uViewD;
uniform vec4 uMark; uniform float uMarkOn;
const vec3 FOG=vec3(0.010,0.013,0.030);
float map(vec4 p){ return 1e3; }
`+D.MAT+D.WALLS+`
float guardShadowW(vec4 P, vec4 Lw){
  float dl=acosh(max(-md(P,Lw),1.)); vec4 tl=tp(Lw,P); float s=1.;
  for(int j=0;j<${NG};j++){ if(j>=uNG) break;
    vec4 C=uG[j]; float dc=acosh(max(-md(P,C),1.)); if(dc>dl||dc<0.02) continue;
    float al=asin(clamp(sinh(0.075)/sinh(dc),0.,1.)), th=acos(clamp(md(tp(C,P),tl),-1.,1.));
    s*=mix(0.25,1.,smoothstep(al*0.5,al*1.7,th)); }
  return s; }
void main(){
  int room=int(vRoom+.5); float lit=uLit[room];
  vec4 Xw=hn(vXw), p=hn(vXl);
  vec4 n=tp(vNl,p), v=-tp(uCamL[room],p);
  if(md(n,v)>0.) n=-n;
  // складываем точку (и векторы) в фундаментальную область комнаты — там заданы материалы стен
  for(int it=0;it<24;it++){ bool any=false;
    for(int k=1;k<4;k++){ float s=md(p,uM[k]); if(s>1e-7){ p-=2.*s*uM[k]; n-=2.*md(n,uM[k])*uM[k]; v-=2.*md(v,uM[k])*uM[k]; any=true; } }
    if(!any) break; }
  int mt=int(vTex.x+.5);
  vec4 L=tp(vec4(0,0,0,1),p); float sr=sinh(acosh(max(p.w,1.)));
  float att=1.6/(0.18+sr*sr)*lit;
  vec3 sc;
  if(mt==2) sc=lampShade(n,v,uLampC,lit);
  else{
    vec3 base; float metal=1., rough;
    if(mt==1||mt==3){ gId=1; if(mt==1) n=bumpN(p,n,1,1.);
      brass(p,base,rough); float u=alongEdge(p); float gb=abs(fract(u*13.)-0.5)/13.; if(mt==1) base*=mix(0.40,1.,smoothstep(0.002,0.006,gb));
      if(uPal==1){ base=vec3(0.30,0.29,0.28)*(mt==1? mix(0.5,1.,smoothstep(0.002,0.006,gb)):1.); rough=0.5; } }
    else{ gId=5; n=bumpN(p,n,5,1.); wallMat(p,room,base,metal,rough);
      if(mt==4){ // решётка запечатанной грани: кованые прутья, сквозь неё видно
        vec3 k=vXl.xyz/vXl.w; float gx=abs(fract(dot(k,vec3(7.,3.,5.))*2.2)-.5), gy=abs(fract(dot(k,vec3(-3.,7.,2.))*2.2)-.5);
        if(min(gx,gy)>0.07&&edgeDist(p)>0.13) discard;
        base=vec3(0.16,0.16,0.17)*(0.7+0.5*fbm(p.xyz*40.)); metal=1.; rough=0.5; } }
    if(lit>0.) att*=guardShadowW(Xw,uRoomC[room]);
    sc=brdf(base,metal,rough,n,v,L,p)*uLampC*att+ambEnv(n,v,L,uLampC,att,base,metal,rough,1.);
    if(uStraight>0.){ if(mt==1) sc+=vec3(1.0,0.96,0.88)*uStraight*1.6*(0.55+0.45*sin(uTime*9.+alongEdge(p)*40.)); else sc=mix(sc,vec3(0.8,0.82,0.86)*(0.3+0.7*lit),0.35*uStraight); }
  }
  float t=acosh(max(-md(uCamW,Xw),1.));
  vec3 col=mix(FOG,sc,exp(-t/uFog));
  if(uLens>0.){
    col=mix(col,vec3(dot(col,vec3(.3,.5,.2)))*vec3(0.55,0.8,1.25),0.45*uLens);
    for(int j=0;j<${NG};j++){ if(j>=uNG) break;
      float dist=acosh(max(-md(Xw,uG[j]),1.)); if(dist>uViewD||dist<0.02) continue;
      if(md(tp(Xw,uG[j]),uGD[j])>uCosFov) col=mix(col,vec3(1.,0.18,0.08),0.28*uLens*(1.-dist/uViewD)); }
  }
  if(uMarkOn>.5){ float dm=acosh(max(-md(Xw,uMark),1.)); col+=vec3(0.55,0.92,1.0)*1.6*exp(-dm*dm/0.006); }
  if(uTime<0.) col=vec3(float(mt)*0.25+0.05,att*0.2,sr);
  fragColor=outc(col,t);
}`;
// ───────── шейдеры объектов: прежняя формула внутри экранного прямоугольника объекта ─────────
const VS_OBJ=`#version 300 es
in vec4 aPos;
void main(){ gl_Position=aPos; }`;
const FS_OBJ=D.HEAD+`
uniform vec3 uLampC; uniform mat4 uVM; uniform mat4 uPM; uniform float uGhost;
const vec3 FOG=vec3(0.010,0.013,0.030);
`+D.LIGHT+D.OBJ_SDF+D.OBJ_H+`
void main(){
  vec2 uv=(2.*gl_FragCoord.xy-uRes)/uRes.y;
  vec3 dr=normalize(vec3(uv*uTanFov,1.));
  vec4 p0=uCam[3], v0=uCam[0]*dr.x+uCam[1]*dr.y+uCam[2]*dr.z;
  traceObjects(p0,v0);
  if(gIO<0) discard;
  float t=gTO; vec4 X=cosh(t)*p0+sinh(t)*v0;
  vec4 c=uVM*X; vec4 cl=uPM*vec4(c.xy,-c.z,c.w); gl_FragDepth=clamp(cl.z/cl.w*.5+.5,0.,1.);
  if(uGhost>.5){ fragColor=vec4(vec3(1.,0.42,0.18)*0.5,1.); return; }
  vec3 col=mix(FOG,shadeObject(p0,v0,uLampC),exp(-t/uFog));
  if(uLens>0.) col=mix(col,vec3(dot(col,vec3(.3,.5,.2)))*vec3(0.55,0.8,1.25),0.45*uLens);
  fragColor=outc(col,t);
}`;
let PR=null,PO=null,err=null;
try{PR=compile(VS_ROOM,FS_ROOM);PO=compile(VS_OBJ,FS_OBJ);}catch(e){err=e;console.error('raster shaders',e);}

// ───────── сетка уровня ─────────
function polytope(U,RI){const n=U.length,V=[];
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)for(let k=j+1;k<n;k++){const a=U[i],b=U[j],c=U[k],d=dot(a,cross(b,c));if(Math.abs(d)<1e-6)continue;
    const x=sc(add(add(cross(b,c),cross(c,a)),cross(a,b)),RI/d);if(U.some(u=>dot(u,x)>RI+1e-6))continue;if(V.some(v=>Math.hypot(...sub(v,x))<1e-6))continue;V.push(x);}
  const FV=U.map(u=>{const vs=V.filter(v=>Math.abs(dot(u,v)-RI)<1e-6),c=sc(u,RI),e1=nrm(sub(vs[0],c)),e2=cross(u,e1);
    return vs.map(v=>({v,a:Math.atan2(dot(sub(v,c),e2),dot(sub(v,c),e1))})).sort((p,q)=>p.a-q.a).map(p=>p.v);});
  const E=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){const vs=V.filter(v=>Math.abs(dot(U[i],v)-RI)<1e-6&&Math.abs(dot(U[j],v)-RI)<1e-6);if(vs.length===2)E.push({a:vs[0],b:vs[1],i,j});}
  return {V,FV,E};}
const cache=new Map();
function bake(ctx){const {R,U,RI,RF,roomAt,sealed}=ctx;const PT=polytope(U,RI);
  const P=[],N=[],T=[],RM=[];let room=0,flip=false;
  const tri=(a,b,c,na,nb,nc,m)=>{if((dot(cross(sub(b,a),sub(c,a)),na)<0)!==flip){[b,c]=[c,b];[nb,nc]=[nc,nb];}
    for(const [p,n] of [[a,na],[b,nb],[c,nc]]){P.push(...p);N.push(...n);T.push(m,0,0);RM.push(room);}};
  const quad=(a,b,c,d,na,nb,nc,nd,m)=>{tri(a,b,c,na,nb,nc,m);tri(a,c,d,na,nc,nd,m);};
  const DOOR=0.80,FR=0.90,LIFT=0.03;
  R.forEach((q,ri)=>{room=ri;flip=det4(q.T)<0;
    PT.FV.forEach((vs,k)=>{const u=U[k],n=sc(u,-1),c=sc(u,RI),m=vs.length;const at=(i,s,h)=>add(add(c,sc(sub(vs[(i+m)%m],c),s)),sc(n,h||0));
      const j=roomAt(apply(mul(q.T,RF[k]),[0,0,0,1]));const kind=j<0?0:sealed(ri,j)?4:-1;
      for(let i=0;i<m;i++){
        if(kind>=0){tri(c,at(i,1),at(i+1,1),n,n,n,kind);continue;}                                  // глухая стена или решётка
        const e=nrm(sub(at(i+1,1),at(i,1))),out=nrm(cross(e,n)),nin=nrm(add(sc(n,0.5),out)),nout=nrm(add(n,sc(out,-0.8)));
        quad(at(i,1),at(i,FR,LIFT),at(i+1,FR,LIFT),at(i+1,1),nout,nout,nout,nout,3);                 // портал: скос от ребра
        quad(at(i,FR,LIFT),at(i,DOOR,LIFT),at(i+1,DOOR,LIFT),at(i+1,FR,LIFT),n,n,n,n,3);
        quad(at(i,DOOR,LIFT),at(i,DOOR),at(i+1,DOOR),at(i+1,DOOR,LIFT),nin,nin,nin,nin,3);
      }});
    // балки вдоль рёбер: четверть-валик внутри комнаты
    for(const E of PT.E){const {a,b}=E,e=nrm(sub(b,a)),mid=sc(add(a,b),-0.5);let d1=nrm(cross(e,U[E.i])),d2=nrm(cross(U[E.j],e));
      if(dot(d1,mid)<0)d1=sc(d1,-1);if(dot(d2,mid)<0)d2=sc(d2,-1);const RB=0.045,SEG=4,dir=t=>nrm(add(sc(d1,1-t),sc(d2,t)));
      for(let s=0;s<SEG;s++){const n0=dir(s/SEG),n1=dir((s+1)/SEG);quad(add(a,sc(n0,RB)),add(a,sc(n1,RB)),add(b,sc(n1,RB)),add(b,sc(n0,RB)),n0,n1,n1,n0,1);}}
    // узлы в вершинах: латунные шары (видимая из комнаты часть)
    for(const v of PT.V){const RV=0.075,LA=5,LO=8,ax=nrm(sc(v,-1)),t1=nrm(cross(ax,Math.abs(ax[0])<0.9?[1,0,0]:[0,1,0])),t2=cross(ax,t1);
      const pt=(i,j)=>{const th=Math.PI*0.62*i/LA,ph=2*Math.PI*j/LO;return add(add(sc(ax,Math.cos(th)),sc(t1,Math.sin(th)*Math.cos(ph))),sc(t2,Math.sin(th)*Math.sin(ph)));};
      for(let i=0;i<LA;i++)for(let j=0;j<LO;j++){const A=pt(i,j),B=pt(i+1,j),C=pt(i+1,j+1),Dd=pt(i,j+1);quad(add(v,sc(A,RV)),add(v,sc(B,RV)),add(v,sc(C,RV)),add(v,sc(Dd,RV)),A,B,C,Dd,3);}}
    // лампа
    {const RL=0.055,LA=10,LO=16,pt=(i,j)=>{const th=Math.PI*i/LA,ph=2*Math.PI*j/LO;return [Math.sin(th)*Math.cos(ph),Math.cos(th),Math.sin(th)*Math.sin(ph)];};
      for(let i=0;i<LA;i++)for(let j=0;j<LO;j++){const A=pt(i,j),B=pt(i+1,j),C=pt(i+1,j+1),Dd=pt(i,j+1);quad(sc(A,RL),sc(B,RL),sc(C,RL),sc(Dd,RL),A,B,C,Dd,2);}}
  });
  const vao=gl.createVertexArray();gl.bindVertexArray(vao);const bufs=[];
  const vb=(data,l,size)=>{const b=gl.createBuffer();bufs.push(b);gl.bindBuffer(gl.ARRAY_BUFFER,b);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(data),gl.STATIC_DRAW);gl.enableVertexAttribArray(l);gl.vertexAttribPointer(l,size,gl.FLOAT,false,0,0);};
  vb(P,0,3);vb(N,1,3);vb(T,2,3);vb(RM,3,1);gl.bindVertexArray(null);
  if(/[?&]rdbg=1/.test(location.search)){const cnt={};for(let i=0;i<T.length;i+=3)cnt[T[i]]=(cnt[T[i]]||0)+1;console.log('raster bake',JSON.stringify(cnt),'verts',P.length/3,'faces',PT.FV.length,'edges',PT.E.length,'V',PT.V.length);}
  return {vao,bufs,n:P.length/3};}
function mesh(ctx){const {R,sealed}=ctx;let key='';for(let i=0;i<R.length;i++)for(let j=i+1;j<R.length;j++)if(sealed(i,j))key+=i+'-'+j+';';
  let c=cache.get(ctx.A);if(c&&c.key===key)return c.m;
  if(c){gl.deleteVertexArray(c.m.vao);c.m.bufs.forEach(b=>gl.deleteBuffer(b));}
  const m=bake(ctx);cache.set(ctx.A,{key,m});if(cache.size>3){const k=cache.keys().next().value;const o=cache.get(k);gl.deleteVertexArray(o.m.vao);o.m.bufs.forEach(b=>gl.deleteBuffer(b));cache.delete(k);}
  return m;}

// ───────── кадр ─────────
const quadVao=gl.createVertexArray(),quadBuf=gl.createBuffer();gl.bindVertexArray(quadVao);gl.bindBuffer(gl.ARRAY_BUFFER,quadBuf);
gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(24),gl.DYNAMIC_DRAW);gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,4,gl.FLOAT,false,0,0);gl.bindVertexArray(null);
const FULL=new Float32Array([-1,-1,0,1, 1,-1,0,1, 1,1,0,1, -1,-1,0,1, 1,1,0,1, -1,1,0,1]);
// экранный прямоугольник, накрывающий шар радиуса Rb вокруг объекта (или весь экран, если камера рядом)
function objQuad(o,Rb,Vm,Pm){const c=apply(Vm,o.pos),d=Math.acosh(Math.max(c[3],1));if(d<Rb*1.3)return FULL;
  const sa=Math.sinh(Rb)/Math.sinh(d);if(sa>0.85)return FULL;const ta=sa/Math.sqrt(1-sa*sa)*1.08;
  const dir=nrm([c[0],c[1],c[2]]),e1=nrm(cross(dir,Math.abs(dir[1])<0.9?[0,1,0]:[1,0,0])),e2=cross(dir,e1);
  const corner=(a,b)=>{const k=sc(add(dir,add(sc(e1,a*ta),sc(e2,b*ta))),0.5),v=[k[0],k[1],-k[2],1];return [0,1,2,3].map(r=>Pm[r]*v[0]+Pm[4+r]*v[1]+Pm[8+r]*v[2]+Pm[12+r]*v[3]);};
  const A=corner(-1,-1),B=corner(1,-1),C=corner(1,1),Dd=corner(-1,1);return new Float32Array([...A,...B,...C,...A,...C,...Dd]);}
function rooms(ctx){if(!PR||!PO)return false;const {A,L,R,g,SC,now,objs,S}=ctx;if(R.length>NR)return false;
  const c=S.c,Cw=mul(c.G,c.M),Vm=linv(Cw),f=1/D.fovTan(),asp=SC.sw/SC.sh,n=0.003,fa=1.0;
  const Pm=[f/asp,0,0,0, 0,f,0,0, 0,0,(fa+n)/(n-fa),-1, 0,0,2*fa*n/(n-fa),0];
  const camW=Cw.slice(12,16),M=mesh(ctx),[FOV,VIEW]=D.FOVV();
  gl.clearColor(0.010/1.010,0.013/1.013,0.030/1.030,60/61);gl.clearDepth(1);gl.depthMask(true);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);
  gl.enable(gl.DEPTH_TEST);gl.depthFunc(gl.LESS);gl.disable(gl.BLEND);if(/[?&]nocull=1/.test(location.search))gl.disable(gl.CULL_FACE);else gl.enable(gl.CULL_FACE);gl.cullFace(gl.BACK);gl.frontFace(det4(Cw)<0?gl.CCW:gl.CW);
  // комнаты
  gl.useProgram(PR.pr);let Lc=PR.loc;
  const guards=objs.filter(o=>o.kind===1&&!o.sl).slice(0,NG);
  gl.uniform2f(Lc.uRes,SC.sw,SC.sh);gl.uniform1f(Lc.uDirect,SC.post?0:1);gl.uniform1f(Lc.uFog,L.fog||6.5);
  gl.uniformMatrix4fv(Lc.uVM,false,Vm);gl.uniformMatrix4fv(Lc.uPM,false,Pm);gl.uniformMatrix4fv(Lc.uRoom,false,R.flatMap(q=>q.T));
  gl.uniform4fv(Lc.uCamW,camW);gl.uniform4fv(Lc.uCamL,R.flatMap(q=>apply(linv(q.T),camW)));gl.uniform4fv(Lc.uRoomC,R.flatMap(q=>q.c));
  gl.uniform1fv(Lc.uLit,R.map((q,i)=>S.lit[i]?1:0));
  gl.uniform4fv(Lc.uM,g.M.flat());gl.uniform4fv(Lc.uE1,g.E1);gl.uniform4fv(Lc.uE2,g.E2);if(Lc.uP1)gl.uniform4fv(Lc.uP1,g.P1);
  gl.uniform1i(Lc.uPal,L.pal||0);gl.uniform3fv(Lc.uLampC,L.lamp||[1.0,0.68,0.36]);gl.uniform1f(Lc.uStraight,S.straight||0);gl.uniform1f(Lc.uTime,/[?&]rdbg=2/.test(location.search)?-1:now/1000);
  gl.uniform1f(Lc.uLens,S.lensOn?1:0);gl.uniform1i(Lc.uNG,guards.length);gl.uniform1f(Lc.uCosFov,Math.cos(FOV/2));gl.uniform1f(Lc.uViewD,VIEW);
  if(guards.length){gl.uniform4fv(Lc.uG,guards.flatMap(o=>o.pos));gl.uniform4fv(Lc.uGD,guards.flatMap(o=>o.F.slice(8,12)));}
  const mk=ctx.mark;gl.uniform1f(Lc.uMarkOn,mk?1:0);if(mk)gl.uniform4fv(Lc.uMark,mk);
  gl.bindVertexArray(M.vao);gl.drawArrays(gl.TRIANGLES,0,M.n);
  // объекты
  gl.disable(gl.CULL_FACE);gl.useProgram(PO.pr);Lc=PO.loc;gl.bindVertexArray(quadVao);gl.bindBuffer(gl.ARRAY_BUFFER,quadBuf);
  gl.uniform2f(Lc.uRes,SC.sw,SC.sh);gl.uniform1f(Lc.uDirect,SC.post?0:1);gl.uniform1f(Lc.uFog,L.fog||6.5);gl.uniform1f(Lc.uTanFov,D.fovTan());
  gl.uniformMatrix4fv(Lc.uCam,false,Cw);gl.uniformMatrix4fv(Lc.uVM,false,Vm);gl.uniformMatrix4fv(Lc.uPM,false,Pm);gl.uniform3fv(Lc.uLampC,L.lamp||[1.0,0.68,0.36]);
  const B=D.BOUND();
  const drawObj=o=>{D.setObjects(Lc,[o],x=>x,now);gl.bufferSubData(gl.ARRAY_BUFFER,0,objQuad(o,(B[o.kind]||0.08)*(o.kind===16?1.05:1.15),Vm,Pm));gl.drawArrays(gl.TRIANGLES,0,6);};
  gl.uniform1f(Lc.uGhost,0);for(const o of objs)drawObj(o);
  if(S.lensOn&&guards.length){ // Линза: силуэты стражей сквозь стены
    gl.depthFunc(gl.GREATER);gl.depthMask(false);gl.enable(gl.BLEND);gl.blendFunc(gl.ONE,gl.ONE);gl.colorMask(true,true,true,false);gl.uniform1f(Lc.uGhost,1);
    for(const o of guards)drawObj(o);
    gl.colorMask(true,true,true,true);gl.disable(gl.BLEND);gl.depthMask(true);gl.depthFunc(gl.LESS);}
  gl.bindVertexArray(null);gl.disable(gl.DEPTH_TEST);gl.frontFace(gl.CCW);
  return true;}
return {on:!/[?&]rm=1/.test(location.search),rooms,get ok(){return !!(PR&&PO);},err};
}
