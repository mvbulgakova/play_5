'use strict';
// ═══════════════ Пост-обработка: HDR → свечение → «живопись» → тон и цвет ═══════════════
// Сцена рендерится в текстуру с пониженным разрешением (адаптивный scale): цвет хранится
// сжатым c/(1+c), в альфе — расстояние по лучу t/(1+t). Дальше:
//   1) цепочка свечения (bloom): порог с мягким коленом, 5 уровней вниз и тент-фильтр вверх;
//   2) итоговый проход в полном разрешении экрана: фильтр Кувахары (масляная живопись,
//      заодно прячет низкое разрешение рэймарчинга), контуры по разрыву глубины,
//      ACES-тон, раздельное тонирование (тени — бирюза, света — янтарь), виньетка, зерно.
const POST=(()=>{
const hasF=!!gl.getExtension('EXT_color_buffer_float');
const FMT=hasF?{i:gl.RGBA16F,t:gl.HALF_FLOAT}:{i:gl.RGBA8,t:gl.UNSIGNED_BYTE};
const VSQ=`#version 300 es
out vec2 vUv;
void main(){ vec2 p=vec2(float((gl_VertexID<<1)&2), float(gl_VertexID&2)); vUv=p; gl_Position=vec4(p*2.-1.,0.,1.); }`;
const DEC=`vec3 dec(vec3 c){ return c/max(1.-c,1e-3); } float decT(float a){ return a/max(1.-a,1e-3); }`;
const FS_DOWN=`#version 300 es
precision highp float; in vec2 vUv; out vec4 o;
uniform sampler2D uTex; uniform vec2 uTexel; uniform float uFirst;
${DEC}
vec3 S(vec2 uv){ vec3 c=texture(uTex,uv).rgb; return uFirst>.5? dec(c) : c; }
void main(){
  vec2 d=uTexel;
  vec3 a=S(vUv+d*vec2(-1,-1)), b=S(vUv+d*vec2(1,-1)), c=S(vUv+d*vec2(-1,1)), e=S(vUv+d*vec2(1,1)), m=S(vUv);
  vec3 col=(a+b+c+e)*0.125+m*0.5;
  if(uFirst>.5){ float l=max(col.r,max(col.g,col.b)); float k=0.85, kn=0.5;
    float s=clamp(l-k+kn,0.,2.*kn); s=s*s/(4.*kn); col*=max(s,l-k)/max(l,1e-4); col=min(col,vec3(40.)); }
  o=vec4(col,1.);
}`;
const FS_UP=`#version 300 es
precision highp float; in vec2 vUv; out vec4 o;
uniform sampler2D uTex; uniform vec2 uTexel;
void main(){ vec2 d=uTexel;
  vec3 c=texture(uTex,vUv).rgb*4.
   +(texture(uTex,vUv+vec2(d.x,0)).rgb+texture(uTex,vUv-vec2(d.x,0)).rgb+texture(uTex,vUv+vec2(0,d.y)).rgb+texture(uTex,vUv-vec2(0,d.y)).rgb)*2.
   +(texture(uTex,vUv+d).rgb+texture(uTex,vUv-d).rgb+texture(uTex,vUv+vec2(d.x,-d.y)).rgb+texture(uTex,vUv+vec2(-d.x,d.y)).rgb);
  o=vec4(c/16.,1.); }`;
const FS_FINAL=`#version 300 es
precision highp float; in vec2 vUv; out vec4 o;
uniform sampler2D uScene; uniform sampler2D uBloom; uniform vec2 uSceneTexel; uniform vec2 uRes;
uniform float uTime; uniform float uKuw; uniform float uInk; uniform float uBloomK; uniform float uExpo; uniform float uGrade;
${DEC}
float hash12(vec2 p){ vec3 p3=fract(vec3(p.xyx)*.1031); p3+=dot(p3,p3.yzx+33.33); return fract((p3.x+p3.y)*p3.z); }
vec3 aces(vec3 x){ return clamp((x*(2.51*x+0.03))/(x*(2.43*x+0.59)+0.14),0.,1.); }
vec3 SC(vec2 uv){ return dec(texture(uScene,uv).rgb); }
// Фильтр Кувахары по четырём квадрантам: берём квадрант с наименьшей дисперсией.
vec3 kuwahara(vec2 uv,float far){
  vec2 d=uSceneTexel*uKuw*(0.85+1.5*far);
  vec3 m[4]; vec3 s[4];
  for(int k=0;k<4;k++){ m[k]=vec3(0.); s[k]=vec3(0.); }
  for(int j=0;j<=2;j++) for(int i=0;i<=2;i++){
    vec2 o2=vec2(float(i),float(j))*0.5;
    vec3 c;
    c=SC(uv+vec2(-o2.x,-o2.y)*d); m[0]+=c; s[0]+=c*c;
    c=SC(uv+vec2( o2.x,-o2.y)*d); m[1]+=c; s[1]+=c*c;
    c=SC(uv+vec2(-o2.x, o2.y)*d); m[2]+=c; s[2]+=c*c;
    c=SC(uv+vec2( o2.x, o2.y)*d); m[3]+=c; s[3]+=c*c;
  }
  vec3 best=m[0]/9.; float bv=1e9;
  for(int k=0;k<4;k++){ vec3 mu=m[k]/9.; vec3 va=abs(s[k]/9.-mu*mu); float v=(va.r+va.g+va.b)/(1.+dot(mu,vec3(.33)));
    if(v<bv){bv=v;best=mu;} }
  return best;
}
void main(){
  vec2 uv=vUv;
  float tC=decT(texture(uScene,uv).a), far=smoothstep(0.8,5.,tC);
  vec3 col = uKuw>0.01 ? kuwahara(uv,far) : SC(uv);
  // лёгкая хроматическая аберрация к краям кадра
  vec2 qc=uv-.5; vec2 ca=qc*dot(qc,qc)*0.010*uGrade;
  col.r=mix(col.r,SC(uv+ca).r,0.6); col.b=mix(col.b,SC(uv-ca).b,0.6);
  // контур по разрыву глубины (тушь)
  if(uInk>0.){
    vec2 d=uSceneTexel*1.25;
    float t0=decT(texture(uScene,uv).a);
    float tx=decT(texture(uScene,uv+vec2(d.x,0)).a)+decT(texture(uScene,uv-vec2(d.x,0)).a);
    float ty=decT(texture(uScene,uv+vec2(0,d.y)).a)+decT(texture(uScene,uv-vec2(0,d.y)).a);
    float lap=abs(tx+ty-4.*t0)/(0.25+t0);
    float ink=smoothstep(0.10,0.35,lap)*exp(-t0*0.25);
    // внутренние линии по перепаду яркости — «прорисовка» складок и силуэтов персонажей
    float lx=dot(SC(uv+vec2(d.x,0))-SC(uv-vec2(d.x,0)),vec3(.3,.5,.2)), ly=dot(SC(uv+vec2(0,d.y))-SC(uv-vec2(0,d.y)),vec3(.3,.5,.2));
    float lum=dot(col,vec3(.3,.5,.2)), ge=sqrt(lx*lx+ly*ly)/(0.06+lum);
    ink=max(ink,smoothstep(0.9,2.2,ge)*0.45*(1.-far));
    col=mix(col,col*vec3(0.18,0.20,0.30),ink*uInk);
  }
  col+=texture(uBloom,uv).rgb*uBloomK;
  // анаморфные полосы от ярких ламп (горизонтальный размытый блик, холодный оттенок)
  vec3 stk=vec3(0.); for(int i=1;i<=6;i++){ float o2=float(i)*0.022, w=exp(-float(i)*0.45); stk+=(texture(uBloom,uv+vec2(o2,0.)).rgb+texture(uBloom,uv-vec2(o2,0.)).rgb)*w; }
  col+=stk*vec3(0.55,0.75,1.25)*0.06*uBloomK*uGrade;
  col*=uExpo;
  // раздельное тонирование до тон-маппинга
  float l=dot(col,vec3(0.2126,0.7152,0.0722));
  vec3 shadowTint=vec3(0.86,1.00,1.10), lightTint=vec3(1.10,1.00,0.86);
  col*=mix(vec3(1.),mix(shadowTint,lightTint,smoothstep(0.05,0.9,l)),uGrade);
  col=aces(col);
  // лёгкая десатурация и S-кривая
  float g=dot(col,vec3(0.299,0.587,0.114));
  col=mix(vec3(g),col,mix(1.,0.88,uGrade));
  col=mix(col,col*col*(3.-2.*col),0.35*uGrade);
  col=pow(col,vec3(1./2.2));
  col+=vec3(0.010,0.012,0.022)*uGrade;
  vec2 q=uv-.5; col*=1.-0.55*dot(q,q)*uGrade;
  // фактура холста: тонкое переплетение нитей и пятна грунта
  vec2 fc=gl_FragCoord.xy; float weave=0.5+0.25*(sin(fc.x*1.9)+sin(fc.y*1.9+sin(fc.x*0.13)));
  col*=1.+(weave-0.5)*0.035*uGrade+(hash12(floor(fc/7.))-.5)*0.02*uGrade;
  col+=(hash12(gl_FragCoord.xy+fract(uTime*7.31)*391.)-.5)*0.035*uGrade;
  o=vec4(col,1.);
}`;
function prog(fs){const mk=(t,s)=>{const sh=gl.createShader(t);gl.shaderSource(sh,s);gl.compileShader(sh);
    if(!gl.getShaderParameter(sh,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(sh));return sh;};
  const p=gl.createProgram();gl.attachShader(p,mk(gl.VERTEX_SHADER,VSQ));gl.attachShader(p,mk(gl.FRAGMENT_SHADER,fs));gl.linkProgram(p);
  if(!gl.getProgramParameter(p,gl.LINK_STATUS))throw new Error(gl.getProgramInfoLog(p));
  const loc={};const n=gl.getProgramParameter(p,gl.ACTIVE_UNIFORMS);for(let i=0;i<n;i++){const u=gl.getActiveUniform(p,i);loc[u.name]=gl.getUniformLocation(p,u.name);}
  return {p,loc};}
let P=null,ok=true;
try{P={down:prog(FS_DOWN),up:prog(FS_UP),fin:prog(FS_FINAL)};}catch(e){console.error(e);ok=false;}
function target(w,h){const tex=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,tex);
  gl.texImage2D(gl.TEXTURE_2D,0,FMT.i,w,h,0,gl.RGBA,FMT.t,null);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.CLAMP_TO_EDGE);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.CLAMP_TO_EDGE);
  const fb=gl.createFramebuffer();gl.bindFramebuffer(gl.FRAMEBUFFER,fb);gl.framebufferTexture2D(gl.FRAMEBUFFER,gl.COLOR_ATTACHMENT0,gl.TEXTURE_2D,tex,0);
  const st=gl.checkFramebufferStatus(gl.FRAMEBUFFER);gl.bindFramebuffer(gl.FRAMEBUFFER,null);
  if(st!==gl.FRAMEBUFFER_COMPLETE)throw new Error('framebuffer '+st);return {tex,fb,w,h};}
function free(t){if(!t)return;gl.deleteTexture(t.tex);gl.deleteFramebuffer(t.fb);}
let scene=null,chain=[];
const LV=5;
function ensure(w,h){if(scene&&scene.w===w&&scene.h===h)return;
  free(scene);chain.forEach(free);scene=target(w,h);chain=[];
  let cw=w,ch=h;for(let i=0;i<LV;i++){cw=Math.max(1,cw>>1);ch=Math.max(1,ch>>1);chain.push(target(cw,ch));}}
// настройки «живописности»: можно ослабить, если кому-то покажется слишком
const cfg={kuw:1,ink:0.55,bloom:0.9,expo:1.0,grade:1};
// Возвращает размер сцены; рисовать её нужно после begin(), затем вызвать end().
function begin(sw,sh){if(!ok)return false;try{ensure(sw,sh);}catch(e){console.error(e);ok=false;return false;}
  gl.bindFramebuffer(gl.FRAMEBUFFER,scene.fb);gl.viewport(0,0,sw,sh);return true;}
function draw(pr,tex,dst){gl.bindFramebuffer(gl.FRAMEBUFFER,dst?dst.fb:null);gl.useProgram(pr.p);
  gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,tex);gl.uniform1i(pr.loc.uTex,0);gl.drawArrays(gl.TRIANGLES,0,3);}
function end(now){
  if(!ok)return;gl.disable(gl.BLEND);
  // вниз
  let src=scene;
  for(let i=0;i<LV;i++){const d=chain[i];gl.viewport(0,0,d.w,d.h);gl.useProgram(P.down.p);
    gl.uniform2f(P.down.loc.uTexel,1/src.w,1/src.h);gl.uniform1f(P.down.loc.uFirst,i===0?1:0);draw(P.down,src.tex,d);src=d;}
  // вверх с накоплением
  gl.enable(gl.BLEND);gl.blendFunc(gl.ONE,gl.ONE);
  for(let i=LV-1;i>0;i--){const s=chain[i],d=chain[i-1];gl.viewport(0,0,d.w,d.h);gl.useProgram(P.up.p);
    gl.uniform2f(P.up.loc.uTexel,1/s.w,1/s.h);draw(P.up,s.tex,d);}
  gl.disable(gl.BLEND);
  // итог в экран
  gl.bindFramebuffer(gl.FRAMEBUFFER,null);gl.viewport(0,0,canvas.width,canvas.height);
  const F=P.fin,L=F.loc;gl.useProgram(F.p);
  gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,scene.tex);gl.uniform1i(L.uScene,0);
  gl.activeTexture(gl.TEXTURE1);gl.bindTexture(gl.TEXTURE_2D,chain[0].tex);gl.uniform1i(L.uBloom,1);
  gl.uniform2f(L.uSceneTexel,1/scene.w,1/scene.h);gl.uniform2f(L.uRes,canvas.width,canvas.height);
  gl.uniform1f(L.uTime,now/1000);
  // радиус Кувахары растёт, когда сцена рендерится грубее экрана
  const up=canvas.width/scene.w;gl.uniform1f(L.uKuw,cfg.kuw*clamp(0.9+0.35*up,1,2.6));
  gl.uniform1f(L.uInk,cfg.ink);gl.uniform1f(L.uBloomK,cfg.bloom*0.22);gl.uniform1f(L.uExpo,cfg.expo);gl.uniform1f(L.uGrade,cfg.grade);
  gl.drawArrays(gl.TRIANGLES,0,3);gl.activeTexture(gl.TEXTURE0);}
return {get ok(){return ok;},begin,end,cfg,hasFloat:hasF};
})();
