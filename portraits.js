'use strict';
// ═══════════════ Портреты: «бронзированные силуэты» ═══════════════
// Силуэтный профиль — модный портретный жанр 1820–1840-х, времени Лобачевского и Бойяи.
// Чёрная фигура на светлом поле, детали — тонкой золотой прорисовкой (так делали «бронзированные»
// силуэты). Каждый портрет собирается из базового профиля и узнаваемых признаков: причёска,
// головной убор, борода, очки, костюм эпохи.
const PORTRAITS=(()=>{
// Катмулл — Ром → кубические Безье (замкнутый или открытый контур)
function smooth(P,closed){const n=P.length,g=i=>P[closed?(i+n)%n:Math.max(0,Math.min(n-1,i))];
  let d=`M${P[0][0]} ${P[0][1]}`;const m=closed?n:n-1;
  for(let i=0;i<m;i++){const p0=g(i-1),p1=g(i),p2=g(i+1),p3=g(i+2);
    const c1=[p1[0]+(p2[0]-p0[0])/6,p1[1]+(p2[1]-p0[1])/6],c2=[p2[0]-(p3[0]-p1[0])/6,p2[1]-(p3[1]-p1[1])/6];
    d+=`C${c1[0].toFixed(1)} ${c1[1].toFixed(1)} ${c2[0].toFixed(1)} ${c2[1].toFixed(1)} ${p2[0]} ${p2[1]}`;}
  return d+(closed?'Z':'');}
const BUST=[[74,118],[90,121],[100,125],[100,140],[0,140],[0,126],[10,121],[24,118]];
const FACE_M=[[34,120],[33,104],[31,96],[26,86],[22,72],[23,58],[28,45],[37,36],[49,31],[60,32],[68,37],[72,45],[73,52],[72,56],[73,59],
  [79,68],[80,70],[77,72],[74,72],[75,76],[73,78],[74,80],[72,82],[73,86],[72,90],[67,93],[62,95],[60,99],[61,106],[64,112]];
const FACE_F=[[35,120],[34,104],[32,96],[27,86],[23,72],[24,58],[29,45],[38,37],[49,32],[60,33],[67,38],[71,46],[72,52],[71,56],[72,59],
  [77,67],[77,69],[75,71],[73,71],[74,75],[72,77],[73,79],[71,81],[71,85],[70,88],[66,91],[61,93],[59,98],[60,106],[62,112]];
const HAIR={
  swept:[[69,38],[72,30],[64,23],[50,20],[36,23],[25,32],[19,46],[19,62],[24,74],[34,68],[50,46],[62,40]],
  bun:[[68,38],[66,31],[54,26],[40,27],[29,34],[23,46],[22,60],[27,70],[38,50],[56,36]],
  short:[[69,37],[68,31],[58,27],[44,27],[32,32],[25,42],[22,56],[25,68],[36,52],[56,36]],
  wavy:[[70,37],[71,29],[62,23],[50,22],[38,22],[28,28],[21,38],[17,52],[19,66],[25,78],[33,66],[50,44],[60,38]],
  classic:[[70,40],[71,32],[63,26],[50,24],[37,26],[27,33],[21,45],[20,60],[24,72],[34,60],[52,42]],
  queue:[[69,38],[67,31],[56,26],[42,26],[30,32],[23,44],[21,58],[24,72],[34,56],[56,38]],
  bald:[[31,60],[24,62],[23,74],[28,82],[34,72]],
  hood:[[73,42],[71,24],[56,13],[37,14],[20,30],[13,56],[14,84],[20,110],[42,120],[34,92],[30,60],[44,34],[62,32]],
  cap:[[30,42],[34,27],[50,19],[65,22],[73,32],[72,38],[52,33],[33,44]],
  mitre:[[33,40],[38,10],[50,1],[60,7],[68,37],[50,31]],
  biretta:[[29,40],[28,22],[44,17],[62,19],[71,30],[67,38],[50,33]],
};
const BEARD={
  long:[[52,72],[60,84],[70,88],[78,88],[83,96],[83,110],[77,123],[66,126],[58,112],[50,94]],
  full:[[52,74],[62,88],[74,88],[80,94],[80,104],[71,111],[58,105],[48,88]],
  goatee:[[67,86],[77,86],[80,96],[73,102],[65,94]],
  mustache:[[71,73],[79,73],[81,77],[73,77]],
};
const COLLAR={
  collar:[[61,103],[70,99],[75,107],[66,113]],
  uniform:[[60,104],[70,102],[72,112],[61,113]],
  jabot:[[64,112],[76,116],[73,121],[78,126],[70,128],[66,120]],
  dress:[[59,104],[66,104],[68,110],[62,112]],
};
function gilt(f,o){const L=[];const s=(d,w)=>L.push(`<path d="${d}" stroke-width="${w||0.7}"/>`);
  // ухо, глаз, бровь
  if(!(o.hair==='hood'))s('M44 58c-4 1-5 8-1 12c3 2 5 0 4-3');
  s(f?'M64 56q3-1 5 0':'M65 55q3-1 5 0');s(f?'M63 51q4-2 8 0':'M63 50q4-2 8 1',0.6);
  const h=o.hair;
  if(h==='swept')s('M66 30q-12-6-28 0M60 26q-16 0-30 14M54 24q-18 4-30 26M30 64q-4-12 2-24');
  if(h==='bun')s('M62 32q-14-4-26 6M56 30q-16 2-26 18'),s('M17 48q8-6 14 2');
  if(h==='short'||h==='classic')s('M64 30q-12-3-24 3M56 28q-14 2-24 16');
  if(h==='classic')s('M70 38q-20-8-44 2',1.1);
  if(h==='wavy')s('M66 27q-8 2-14-2q-8 4-14 0q-8 4-12 10M24 50q4 6 0 12q4 6 2 12');
  if(h==='queue')s('M60 29q-14 0-26 12'),s('M27 74l-7 4l2 6l6-4M27 74l-2 8l6 2',0.9);
  if(h==='cap')s('M33 43q20-11 39-5',1.1),s('M27 50q-2 8 0 14M24 66q2 5 6 6');
  if(h==='mitre')s('M44 10v14h14M47 13v8h8',1);
  if(h==='biretta')s('M36 22v14M50 18v14M63 21v12');
  if(h==='hood')s('M70 30q-14-18-36-12M16 60q2 30 10 54',0.9);
  if(h==='bald')s('M40 34q10-4 22 0',0.5);
  if(o.side)s('M48 64l1 14M51 63l1 14M54 64l1 12M45 66l1 10',0.6);
  if(o.beard==='long'||o.beard==='full')s('M60 96q2 8-2 16M66 100q1 8-3 14M54 92q0 10-4 16');
  const b=o.bust;
  if(b==='collar')s('M61 103l9-4l5 8M66 113l4 6l-6 3M72 116q10 2 20 8M56 112q-4 8-2 18',0.8);
  if(b==='uniform')s('M60 104l10-2l2 10M78 120v2M84 122v2M90 124v2',1),s('M6 117q8-6 18 0',1.2);
  if(b==='toga')s('M30 120q20 6 40 2M20 124q30 10 60 4M60 116q-6 10-2 22',0.8);
  if(b==='coat')s('M62 112q6 8 4 26M66 112q10 6 24 10',0.8);
  if(b==='tie')s('M62 110l6 4l-2 22M68 114l4 22',0.8);
  if(b==='jabot')s('M68 116q4 4 0 8',0.8);
  if(b==='clerical')s('M58 108q6 4 12 2',1.2);
  if(b==='dress')s('M58 112q10 4 20 2M60 108q3 2 6 0',0.8);
  if(b==='hood')s('M30 118q20 10 50 4',0.8);
  if(o.acc==='goggles')s('M30 44q18-10 40-6',1);
  if(o.acc==='monocle')s('M76 60q-6 16-10 34',0.5);
  return `<g fill="none" stroke="url(#pg)" stroke-linecap="round">${L.join('')}</g>`;}
function svg(o,cls){const f=!!o.female;const ink='#141a2e';
  const shapes=[smooth([...(f?FACE_F:FACE_M),...BUST],true)];
  if(o.hair&&HAIR[o.hair])shapes.push(smooth(HAIR[o.hair],true));
  if(o.hair==='bun')shapes.push('M14 52a10 10 0 1 0 20 0a10 10 0 1 0-20 0Z');
  if(o.hair==='biretta')shapes.push('M45 14a3.5 3.5 0 1 0 7 0a3.5 3.5 0 1 0-7 0Z');
  if(o.beard&&BEARD[o.beard])shapes.push(smooth(BEARD[o.beard],true));
  const cb=o.bust==='collar'||o.bust==='coat'||o.bust==='tie'?'collar':o.bust;if(COLLAR[cb])shapes.push(smooth(COLLAR[cb],true));
  if(o.bust==='uniform')shapes.push(smooth([[4,124],[6,115],[16,112],[26,117]],true));
  if(o.bust==='toga')shapes.push(smooth([[18,118],[34,110],[44,116],[30,126]],true));
  let extra='';
  if(o.acc==='goggles')extra+=`<ellipse cx="71" cy="38" rx="5" ry="4" fill="${ink}"/><ellipse cx="72" cy="38" rx="2.4" ry="2" fill="url(#pg)"/>`;
  if(o.acc==='monocle')extra+=`<circle cx="76" cy="56" r="4.2" fill="none" stroke="${ink}" stroke-width="1.6"/><circle cx="76" cy="56" r="4.2" fill="none" stroke="url(#pg)" stroke-width=".5"/>`;
  if(o.acc==='pincenez')extra+=`<ellipse cx="76.5" cy="56" rx="2.4" ry="3.6" fill="none" stroke="${ink}" stroke-width="1.3"/>`;
  return `<svg class="${cls||'portrait'}" viewBox="0 0 100 120" aria-hidden="true"><defs>
  <linearGradient id="pg" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#f6dca2"/><stop offset=".5" stop-color="#d6a35a"/><stop offset="1" stop-color="#9a6b33"/></linearGradient>
  <radialGradient id="pb" cx=".45" cy=".4" r=".7"><stop offset="0" stop-color="#f3e8cf"/><stop offset=".75" stop-color="#d9c6a0"/><stop offset="1" stop-color="#a88c5e"/></radialGradient>
  <clipPath id="pc"><ellipse cx="50" cy="60" rx="43" ry="53"/></clipPath></defs>
  <ellipse cx="50" cy="60" rx="43" ry="53" fill="url(#pb)"/>
  <g clip-path="url(#pc)" transform="translate(6 4) scale(.9)">${shapes.map(d=>`<path d="${d}" fill="${ink}"/>`).join('')}${extra}${gilt(f,o)}</g>
  <ellipse cx="50" cy="60" rx="45.5" ry="55.5" fill="none" stroke="url(#pg)" stroke-width="3"/>
  <ellipse cx="50" cy="60" rx="48.5" ry="58.5" fill="none" stroke="url(#pg)" stroke-width=".8" stroke-dasharray="1.2 2.2"/></svg>`;}
// Персонажи игры и исторические авторы лемм
const P={
  vera:{name:'Вера',sub:'чертёжница Церкви',female:1,hair:'bun',acc:'goggles',bust:'dress'},
  nikolai:{name:'Николай-Геометр',sub:'Странник',hair:'swept',side:1,bust:'collar'},
  euclid:{name:'Архипрелат Евклид',sub:'глава Церкви Пятого Постулата',hair:'mitre',beard:'long',bust:'toga'},
  oricycla:{name:'Сестра Орицикла',sub:'Криволинейные',female:1,hair:'hood',bust:'hood'},
  kassel:{name:'Циркулятор Кассель',sub:'мерило дефекта',hair:'short',acc:'monocle',bust:'uniform'},
  bernhard:{name:'Бернхард',sub:'посланник Эллиптиков',hair:'short',beard:'full',bust:'coat'},
  ortt:{name:'Старший чертёжник Ортт',sub:'Чертёжная Собора',hair:'bald',side:1,beard:'mustache',bust:'collar'},
  guard:{name:'Чертёжник',sub:'патруль Церкви',hair:'hood',bust:'hood'},
  // исторические лица
  h_euclid:{name:'Евклид',sub:'«Начала», ок. 300 до н. э.',cond:'Подлинных изображений Евклида не существует; силуэт условный.',hair:'classic',beard:'long',bust:'toga'},
  saccheri:{name:'Джироламо Саккери',sub:'1667–1733',cond:'Прижизненный портрет нам не известен; силуэт условный — облачение иезуита.',hair:'biretta',bust:'clerical'},
  lambert:{name:'Иоганн Генрих Ламберт',sub:'1728–1777',hair:'queue',bust:'jabot'},
  gauss:{name:'Карл Фридрих Гаусс',sub:'1777–1855',hair:'cap',bust:'collar'},
  lobachevsky:{name:'Николай Иванович Лобачевский',sub:'1792–1856',hair:'swept',bust:'collar'},
  wachter:{name:'Фридрих Людвиг Вахтер',sub:'1792–1817',cond:'Прижизненный портрет нам не известен; силуэт условный.',hair:'wavy',bust:'collar'},
  bolyai:{name:'Янош Бойяи',sub:'1802–1860',cond:'Подлинного портрета Бойяи не сохранилось; распространённое изображение недостоверно. Силуэт условный — мундир военного инженера.',hair:'wavy',beard:'mustache',bust:'uniform'},
  riemann:{name:'Бернхард Риман',sub:'1826–1866',hair:'short',beard:'full',bust:'coat'},
  cayley:{name:'Артур Кэли',sub:'1821–1895',hair:'bald',side:1,bust:'coat'},
  beltrami:{name:'Эудженио Бельтрами',sub:'1835–1900',hair:'short',beard:'goatee',bust:'coat'},
  klein:{name:'Феликс Клейн',sub:'1849–1925',hair:'short',beard:'long',bust:'coat'},
  poincare:{name:'Анри Пуанкаре',sub:'1854–1912',hair:'short',beard:'full',acc:'pincenez',bust:'coat'},
  minkowski:{name:'Герман Минковский',sub:'1864–1909',hair:'short',beard:'mustache',acc:'pincenez',bust:'coat'},
  coxeter:{name:'Гарольд Скотт Макдональд Кокстер',sub:'1907–2003',hair:'short',bust:'tie'},
};
return {svg:(id,cls)=>svg(P[id]||P.guard,cls),info:id=>P[id]||P.guard,list:P};
})();
