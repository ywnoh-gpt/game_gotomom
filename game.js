'use strict';
const canvas = document.querySelector('#game'), ctx = canvas.getContext('2d');
const ui = Object.fromEntries(['status','detail','percent','returns','progressFill','progressTrack','start','restart','modeButtons','modeDrag','directionPad','joystick','joystickKnob','controlHint','stage','sceneOverlay','overlayTitle','overlayDetail','overlayStart','toast','settingsDialog','openSettings','closeSettings','doneSettings','photoStatus'].map(id => [id, document.querySelector('#'+id)]));
const FIELD = 736, WIDTH = FIELD;
let HEIGHT = 660;
const UNIT = 33, MAP_LENGTH = 121, WORLD = UNIT * MAP_LENGTH;
const keys = new Set(), faces = {hero:null,mom:null};
const Y = progress => WORLD - progress * UNIT;
const clamp = (n,a,b) => Math.max(a,Math.min(b,n));
const zones = [
  {from:0,to:5,name:'안전한 땅 1',sub:'따뜻한 잔디밭에서 출발해요.',color:'#dce9c6',type:'safe'},
  {from:5,to:34,name:'분유 젖병 들판',sub:'젖병과 분유에 닿으면 안전한 땅 1로 돌아가요.',color:'#f4e6c9',type:'bottle'},
  {from:34,to:40,name:'안전한 땅 2',sub:'여기서 잠깐 쉬어요. 다음은 꼬꼬맘 미로!',color:'#dce9c6',type:'safe'},
  {from:40,to:80,name:'움직이는 꼬꼬맘 미로',sub:'가로·세로 벽 사이로! 움직이는 벽의 틈이 열리면 지나가요.',color:'#eee6ca',type:'maze'},
  {from:80,to:85,name:'안전한 땅 3',sub:'마지막 쉼터예요. 유모차가 지나간 뒤에 이동해요.',color:'#dce9c6',type:'safe'},
  {from:85,to:116,name:'쌩쌩 유모차 거리',sub:'빠른 유모차에 닿으면 안전한 땅 3으로 돌아가요.',color:'#dce4e2',type:'stroller'},
  {from:116,to:121,name:'엄마가 기다리는 곳',sub:'조금만 더! 엄마에게 다가가 보세요.',color:'#f3dfe1',type:'goal'}
];
const spawnPoints = [{x:FIELD/2,y:Y(2.5)},{x:FIELD/2,y:Y(37)},{x:FIELD/2,y:Y(82.5)}];
const goal = {x:FIELD/2,y:74};
// A connected maze with real branches, dead ends, and sliding gates on its route.
function buildMaze(){
  const cols=5,rows=8,cell=132,left=38,top=Y(80)+132,thick=42;
  const entry=(rows-1)*cols+3,exit=2;
  let seed=27182;
  const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
  const edge=(a,b)=>Math.min(a,b)+':'+Math.max(a,b);
  const links=new Set(),visited=new Set([entry]),stack=[entry];
  while(stack.length){
    const a=stack[stack.length-1],r=Math.floor(a/cols),c=a%cols;
    const neighbors=[[r-1,c],[r,c+1],[r+1,c],[r,c-1]].filter(([nr,nc])=>nr>=0&&nr<rows&&nc>=0&&nc<cols).map(([nr,nc])=>nr*cols+nc).filter(b=>!visited.has(b));
    if(!neighbors.length){stack.pop();continue;}
    const b=neighbors[Math.floor(random()*neighbors.length)];links.add(edge(a,b));visited.add(b);stack.push(b);
  }
  const fixed=[];
  function runs(flags,emit){for(let start=0;start<flags.length;){if(!flags[start]){start++;continue;}let end=start+1;while(end<flags.length&&flags[end])end++;emit(start,end);start=end;}}
  for(let r=0;r<=rows;r++){
    const closed=Array.from({length:cols},(_,c)=>r===0?c!==exit:r===rows?c!==entry%cols:!links.has(edge((r-1)*cols+c,r*cols+c)));
    runs(closed,(a,b)=>fixed.push({x:left+a*cell-thick/2,y:top+r*cell-thick/2,w:(b-a)*cell+thick,h:thick}));
  }
  for(let c=0;c<=cols;c++){
    const closed=Array.from({length:rows},(_,r)=>c===0||c===cols||!links.has(edge(r*cols+c-1,r*cols+c)));
    runs(closed,(a,b)=>fixed.push({x:left+c*cell-thick/2,y:top+a*cell-thick/2,w:thick,h:(b-a)*cell+thick}));
  }
  const queue=[entry],parent=new Map([[entry,null]]);
  for(let i=0;i<queue.length;i++){const a=queue[i];for(const key of links){const [u,v]=key.split(':').map(Number),b=u===a?v:v===a?u:null;if(b!==null&&!parent.has(b)){parent.set(b,a);queue.push(b);}}}
  const route=[];for(let a=exit;a!==null;a=parent.get(a))route.unshift(a);
  const gates=[];
  for(let i=3;i<route.length-2;i+=4){
    const a=route[i-1],b=route[i],ar=Math.floor(a/cols),br=Math.floor(b/cols),ac=a%cols,bc=b%cols;
    // Retract sideways into a neighboring wall, leaving the passage fully clear.
    const horizontal=ar!==br;
    if(horizontal&&(ac===0||ac===cols-1)||!horizontal&&(ar===0||ar===rows-1))continue;
    gates.push(horizontal
      ?{x:left+ac*cell+thick/2,y:top+Math.max(ar,br)*cell-thick/2,w:cell-thick,h:thick,axis:'x',amplitude:90,rate:.72+gates.length*.055,phase:gates.length*1.6}
      :{x:left+Math.max(ac,bc)*cell-thick/2,y:top+ar*cell+thick/2,w:thick,h:cell-thick,axis:'y',amplitude:90,rate:.72+gates.length*.055,phase:gates.length*1.6});
    if(gates.length===4)break;
  }
  return {walls:fixed,gates,route,cols,rows,cell,left,top,entry,exit};
}
const maze=buildMaze(),walls=maze.walls,movingWalls=maze.gates;
function wallPose(wall,time=elapsed){return {...wall,[wall.axis]:wall[wall.axis]+Math.sin(time*wall.rate+wall.phase)*wall.amplitude};}
function mazeWalls(time=elapsed){return [...walls,...movingWalls.map(w=>wallPose(w,time))];}
let player, camera, running, won, started, elapsed, visualTime=0, last=0, checkpoint, returns, bottles, strollers, particles, toast, lastZone;
let controlMode = 'drag', gesture = null;
const heldButtons = new Map();
function clearControls(){
  const captured=gesture?.id;gesture=null;keys.clear();heldButtons.clear();
  ui.joystick.style.setProperty('--stick-x','0px');ui.joystick.style.setProperty('--stick-y','0px');
  if(captured!==undefined&&ui.joystick.hasPointerCapture(captured))ui.joystick.releasePointerCapture(captured);
}
function chooseMode(mode){
  clearControls();controlMode=mode;
  ui.modeButtons.setAttribute('aria-pressed',String(mode==='buttons'));
  ui.modeDrag.setAttribute('aria-pressed',String(mode==='drag'));
  ui.directionPad.hidden=mode!=='buttons';ui.joystick.hidden=mode!=='drag';
  ui.controlHint.textContent=mode==='drag'
    ?'오른쪽 조이스틱을 밀어요. 손을 떼면 멈춰요.'
    :'아래 방향 버튼을 누르고 있으면 움직여요. 손을 떼면 멈춰요.';
}
ui.modeButtons.onclick=()=>chooseMode('buttons');ui.modeDrag.onclick=()=>chooseMode('drag');
function zoneAt(y) {const p=(WORLD-y)/UNIT;return zones.find(z=>p>=z.from&&p<z.to)||zones[zones.length-1];}
function makeObstacles(){
  bottles=Array.from({length:19},(_,i)=>({x:70+(i*137)%590,y:Y(7.5)-i*45,r:25,vx:(i%2?1:-1)*(68+(i*23)%89),vy:(i%3?1:-1)*(42+(i*17)%55),phase:i*1.7}));
  strollers=[];
  for(let lane=0;lane<9;lane++)for(let j=0;j<(lane%3===1?2:1);j++)strollers.push({x:(lane*157+j*365)%FIELD,y:Y(88+lane*3),vx:(lane%2?-1:1)*(230+(lane%4)*35),w:76,h:60,lane});
}
function setMessage(title,detail){ui.status.textContent=title;ui.detail.textContent=detail;}
function reset(){
  clearControls();player={...spawnPoints[0],r:21,flash:0};camera=WORLD-HEIGHT;running=false;won=false;started=false;elapsed=0;checkpoint=0;returns=0;particles=[];toast=null;lastZone=null;makeObstacles();
  ui.start.textContent='출발! ▶';syncHud();setMessage('안전한 땅 1 · 모험의 시작','위쪽으로 올라가면 엄마를 만날 수 있어요.');
}
function start(){if(ui.settingsDialog.open)return;if(won)reset();running=!running;started=true;clearControls();ui.start.textContent=running?'잠깐 쉬기 Ⅱ':'계속 가기 ▶';if(running){lastZone=null;}else setMessage('잠깐 쉬는 중 🌿','계속 가기를 누르면 그 자리에서 이어서 해요.');syncHud();}
function pauseGame(){clearControls();if(!running)return;running=false;ui.start.textContent='계속 가기 ▶';setMessage('잠깐 쉬는 중 🌿','계속 가기를 누르면 그 자리에서 이어서 해요.');syncHud();}
ui.start.onclick=ui.overlayStart.onclick=start;ui.restart.onclick=reset;
ui.openSettings.onclick=()=>{pauseGame();if(!ui.settingsDialog.open)ui.settingsDialog.showModal();};
ui.closeSettings.onclick=ui.doneSettings.onclick=()=>ui.settingsDialog.close();
ui.settingsDialog.addEventListener('close',clearControls);
function syncHud(){
  const progress=won?MAP_LENGTH:clamp(Math.floor((WORLD-player.y)/UNIT),0,MAP_LENGTH);
  ui.percent.textContent=progress;ui.progressFill.style.width=progress/MAP_LENGTH*100+'%';ui.returns.textContent='쉼터로 돌아간 횟수 '+returns;
  ui.progressTrack.setAttribute('aria-valuenow',String(progress));
  const zone=zoneAt(player.y);if(running&&!won&&zone!==lastZone&&!toast){setMessage(zone.name,zone.sub);lastZone=zone;}
  ui.sceneOverlay.hidden=running;
  ui.sceneOverlay.className='scene-overlay'+(won?' celebration':'');
  ui.overlayTitle.textContent=won?'엄마 품에 도착했어요! 💕':started?'잠깐 쉬어 가요 🌿':'엄마 만나러 떠날까요?';
  ui.overlayDetail.textContent=won?'정말 잘했어! 만나서 행복해 ♥':started?'준비되면 그 자리에서 다시 출발해요.':'사진·설정에서 얼굴을 고르고, 아래 조작부로 위로 올라가요!';
  ui.overlayStart.textContent=won?'한 번 더! ▶':started?'계속 가기 ▶':'출발! ▶';
  ui.toast.hidden=!toast||!running;if(toast)ui.toast.textContent=toast.text;
}
function fitCanvas(){
  const rect=canvas.getBoundingClientRect();if(!rect.width||!rect.height)return;
  const nextHeight=Math.max(100,Math.round(FIELD*rect.height/rect.width));
  if(canvas.width===WIDTH&&HEIGHT===nextHeight)return;
  HEIGHT=nextHeight;canvas.width=WIDTH;canvas.height=HEIGHT;clearControls();
  if(player)camera=won?0:clamp(player.y-HEIGHT*.74,0,Math.max(0,WORLD-HEIGHT));
}
function returnTo(index,reason){
  player.x=spawnPoints[index].x;player.y=spawnPoints[index].y;player.flash=1.4;
  checkpoint=index;returns++;clearControls();camera=clamp(player.y-HEIGHT*.74,0,WORLD-HEIGHT);
  toast={time:2.6,text:reason+' · 안전한 땅 '+(index+1)+'로 돌아왔어요'};
  setMessage('다시 도전해요! 🌿',toast.text);lastZone=null;syncHud();
}
function rectHit(x,y,r,box){const nearX=clamp(x,box.x,box.x+box.w),nearY=clamp(y,box.y,box.y+box.h);return (x-nearX)**2+(y-nearY)**2<r*r;}
function finish(){
  won=true;running=false;clearControls();camera=0;player.x=goal.x-29;player.y=goal.y+12;
  ui.start.textContent='한 번 더! ▶';setMessage('엄마를 만났어요! 사랑해요 💕','작은 발걸음으로 긴 모험을 끝냈어요. 정말 잘했어요!');syncHud();
  particles=Array.from({length:90},(_,i)=>({x:FIELD/2,y:130,vx:(Math.random()-.5)*290,vy:-40-Math.random()*210,life:3+Math.random()*3,color:['#e7a0a2','#edc86d','#92b486','#a2bcd3'][i%4]}));
}
function step(dt){
  elapsed+=dt;player.flash=Math.max(0,player.flash-dt);
  if(toast){toast.time-=dt;if(toast.time<=0){toast=null;lastZone=null;}}
  for(const b of bottles){b.x+=b.vx*dt;b.y+=b.vy*dt;if(b.x<58||b.x>FIELD-58){b.x=clamp(b.x,58,FIELD-58);b.vx*=-1;}if(b.y<Y(34)+60||b.y>Y(5)-60){b.y=clamp(b.y,Y(34)+60,Y(5)-60);b.vy*=-1;}}
  for(const s of strollers){s.x+=s.vx*dt;if(s.x>FIELD+90)s.x=-90;if(s.x< -90)s.x=FIELD+90;}
  const pressed = key=>keys.has(key)||[...heldButtons.values()].includes(key);
  let dx=Number(pressed('ArrowRight')||pressed('d'))-Number(pressed('ArrowLeft')||pressed('a'));
  let dy=Number(pressed('ArrowDown')||pressed('s'))-Number(pressed('ArrowUp')||pressed('w'));
  let speed=210;
  if(gesture&&controlMode==='drag'&&!dx&&!dy){
    dx=gesture.x-gesture.originX;dy=gesture.y-gesture.originY;
    const distance=Math.hypot(dx,dy);
    if(distance<=6){dx=dy=0;}else speed*=clamp((distance-6)/Math.max(1,gesture.radius-6),0,1);
  }
  const len=Math.hypot(dx,dy);player.walking=Boolean(len);if(len){player.x+=dx/len*speed*dt;player.y+=dy/len*speed*dt;}
  player.x=clamp(player.x,48,FIELD-48);player.y=clamp(player.y,28,WORLD-30);
  const p=(WORLD-player.y)/UNIT;
  if(p>=34&&p<40&&checkpoint<1){checkpoint=1;toast={time:2.2,text:'안전한 땅 2 도착! 이제 여기서 다시 시작해요'};setMessage('두 번째 쉼터 도착 🌿',toast.text);}
  if(p>=80&&p<85&&checkpoint<2){checkpoint=2;toast={time:2.2,text:'안전한 땅 3 도착! 엄마까지 마지막 구간이에요'};setMessage('세 번째 쉼터 도착 🌿',toast.text);}
  for(const b of bottles)if(Math.hypot(player.x-b.x,player.y-b.y)<player.r+b.r){returnTo(0,'분유에 닿았어요');return;}
  for(const wall of mazeWalls())if(rectHit(player.x,player.y,player.r,wall)){returnTo(1,'꼬꼬맘 벽에 닿았어요');return;}
  for(const s of strollers)if(rectHit(player.x,player.y,player.r,{x:s.x-s.w/2,y:s.y-s.h/2,w:s.w,h:s.h})){returnTo(2,'유모차에 닿았어요');return;}
  if(Math.hypot(player.x-goal.x,player.y-goal.y)<53)finish();
}
function update(dt){if(running){const count=Math.ceil(dt/.008);for(let i=0;i<count&&running;i++)step(dt/count);if(!won){const aim=clamp(player.y-HEIGHT*.74,0,WORLD-HEIGHT);camera+=(aim-camera)*(1-Math.exp(-dt*10));}syncHud();}}
const sy=y=>y-camera;
function rounded(x,y,w,h,r,fill,stroke){ctx.beginPath();ctx.roundRect(x,y,w,h,r);if(fill){ctx.fillStyle=fill;ctx.fill();}if(stroke){ctx.strokeStyle=stroke;ctx.lineWidth=1.5;ctx.stroke();}}
function circle(x,y,r,color){ctx.beginPath();ctx.arc(x,y,r,0,Math.PI*2);ctx.fillStyle=color;ctx.fill();}
function text(str,x,y,size=16,color='#526345',weight='600'){ctx.textAlign='center';ctx.textBaseline='middle';ctx.font=weight+' '+size+'px system-ui';ctx.fillStyle=color;ctx.fillText(str,x,y);}
function ellipse(x,y,rx,ry,color){ctx.beginPath();ctx.ellipse(x,y,rx,ry,0,0,Math.PI*2);ctx.fillStyle=color;ctx.fill();}
function face(name,x,y,r){circle(x,y+3,r+4,'#35482c18');circle(x,y,r+3,'#fffaf0');const img=faces[name];if(img&&img.naturalWidth&&img.naturalHeight){ctx.save();ctx.beginPath();ctx.arc(x,y,r,0,Math.PI*2);ctx.clip();const s=Math.min(img.naturalWidth,img.naturalHeight);ctx.drawImage(img,(img.naturalWidth-s)/2,(img.naturalHeight-s)/2,s,s,x-r,y-r,r*2,r*2);ctx.restore();}else{circle(x,y,r,name==='hero'?'#f8cfa2':'#efd3b9');text(name==='hero'?'🧒':'👩',x,y+1,r*1.5);}}
function character(name,x,y,r,{walking=false,happy=false}={}){
  const scale=r/21,beat=walking?Math.sin(elapsed*13):Math.sin(visualTime*2)*.2;
  const color=name==='hero'?'#dfb56d':'#e8a1ac';
  ctx.save();ctx.translate(x,y);ctx.scale(scale,scale);
  ellipse(0,42,23,5,'#55613c22');
  const limb=(x1,y1,x2,y2,tint,width)=>{ctx.strokeStyle=tint;ctx.lineWidth=width;ctx.lineCap='round';ctx.beginPath();ctx.moveTo(x1,y1);ctx.lineTo(x2,y2);ctx.stroke();};
  limb(-7,26,-9-beat*3,36,'#ba9472',6);limb(7,26,9+beat*3,36,'#ba9472',6);
  ellipse(-10-beat*3,38,7,4,'#856f53');ellipse(10+beat*3,38,7,4,'#856f53');
  const reach=happy?28:22,leftHandY=happy?-14:21+beat*3,rightHandY=happy?-14:21-beat*3;
  limb(-12,12,-reach,leftHandY,'#f0cba4',6);limb(12,12,reach,rightHandY,'#f0cba4',6);
  circle(-reach,leftHandY,4,'#f3d8b5');circle(reach,rightHandY,4,'#f3d8b5');
  rounded(-14,6,28,24,10,color);circle(0,20,2,'#fff9df');
  ctx.restore();face(name,x,y,r);
}
function flower(x,y){for(let i=0;i<5;i++){const a=i*Math.PI*2/5;circle(x+Math.cos(a)*5,y+Math.sin(a)*5,3.4,'#fff8df');}circle(x,y,2.8,'#deb764');}
const chickenSprites=[];
function chickenSprite(pose){
  if(chickenSprites[pose])return chickenSprites[pose];
  const sprite=document.createElement('canvas');sprite.width=sprite.height=112;
  const g=sprite.getContext('2d');g.scale(2,2);g.translate(28,28);
  const oval=(x,y,rx,ry,color)=>{g.beginPath();g.ellipse(x,y,rx,ry,0,0,Math.PI*2);g.fillStyle=color;g.fill();};
  const dot=(x,y,r,color)=>oval(x,y,r,r,color);
  oval(0,23,23,3,'#676b4f22');
  oval(-11,20,10,4,'#eaa044');oval(11,20,10,4,'#eaa044');
  oval(0,11,19,12,'#2466a5');oval(0,4,18,12,'#a0d5e7');
  oval(-19,3+pose,6,10-pose,'#f2d747');oval(19,5-pose,6,8+pose,'#f2d747');
  oval(-20,3,2,6,'#fff18c55');
  dot(0,-13,12,'#dd4c54');oval(-1,-13,9.5,10,'#fff7e4');
  dot(-1,-25,2.7,'#df5558');dot(4,-24,2.4,'#df5558');
  for(const x of [-4,4]){oval(x,-16,2.8,3.8,'#4e9bb8');oval(x+.5,-16,1.6,2.7,'#253e48');dot(x-.7,-17.3,.9,'white');}
  oval(0,-9,4.5,3.4,'#f1cc3e');oval(0,-7,3,1.5,'#dfa344');
  oval(-3,-1,3,2,'#e76161');oval(3,-1,3,2,'#e76161');dot(0,-1,1.4,'#ba4a51');
  for(let i=0;i<6;i++){g.beginPath();g.arc(-10+(i%3)*10,3+Math.floor(i/3)*7,3,0,Math.PI);g.fillStyle=['#df625b','#fff6da','#eacb45','#4e9ec4','#f0d746','#fcf7de'][i];g.fill();}
  g.strokeStyle='#ffffff55';g.lineWidth=1.8;g.beginPath();g.arc(0,-13,10,Math.PI,Math.PI*1.6);g.stroke();
  chickenSprites[pose]=sprite;return sprite;
}
function chicken(x,y,index,moving){
  const pose=(Math.floor(elapsed*(moving?7:3))+index)%3;
  const size=56*.78;
  ctx.drawImage(chickenSprite(pose),x-size/2,y-size/2,size,size);
}
function drawMazeWall(wall,moving=false,index=0){
  const vertical=wall.h>wall.w,length=vertical?wall.h:wall.w,thickness=vertical?wall.w:wall.h;
  const count=Math.max(1,Math.ceil((length-thickness)/31)+1);
  for(let i=0;i<count;i++){
    const offset=thickness/2+(count===1?0:(length-thickness)*i/(count-1));
    chicken(vertical?wall.x+wall.w/2:wall.x+offset,vertical?sy(wall.y+offset):sy(wall.y+wall.h/2),index+i,moving);
  }
}
function bottle(b){const y=sy(b.y);ctx.save();ctx.translate(b.x,y);ctx.rotate(Math.sin(elapsed*1.6+b.phase)*.12);ellipse(0,25,25,9,'#cab98639');ellipse(-13,24,12,6,'#fff5d7');rounded(-15,-17,30,43,9,'#fffdf4','#bfbaa0');rounded(-12,-1,24,23,6,'#f1d28e');rounded(-17,-20,34,8,3,'#a7c8bf');rounded(-8,-30,16,11,5,'#f1ceb0');for(let i=0;i<3;i++)rounded(3,-9+i*8,6,2,1,'#c2b393');rounded(-10,-12,3,25,2,'#ffffffaa');ctx.restore();}
function stroller(s){const y=sy(s.y);ctx.save();ctx.translate(s.x,y);if(s.vx<0)ctx.scale(-1,1);ellipse(0,25,38,8,'#68777920');ctx.strokeStyle='#738683';ctx.lineWidth=4;ctx.beginPath();ctx.moveTo(-24,-19);ctx.lineTo(-33,-29);ctx.lineTo(-43,-29);ctx.moveTo(-22,-12);ctx.lineTo(22,24);ctx.moveTo(20,-5);ctx.lineTo(-20,23);ctx.stroke();rounded(-28,-10,57,24,8,['#e9bdb6','#a4bdc3','#c1c59a'][s.lane%3]);ctx.beginPath();ctx.arc(6,-9,25,Math.PI,0);ctx.fillStyle=['#dc9e96','#83a9b5','#abb481'][s.lane%3];ctx.fill();ctx.strokeStyle='#ffffff77';ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(6,-33);ctx.lineTo(6,-9);ctx.stroke();for(const x of [-22,23]){circle(x,24,9,'#596760');circle(x,24,4,'#f5efdc');}ctx.strokeStyle='#ffffff90';ctx.lineWidth=2;for(let i=0;i<3;i++){ctx.beginPath();ctx.moveTo(-46-i*7,0+i*7);ctx.lineTo(-59-i*7,0+i*7);ctx.stroke();}ctx.restore();}
function landscape(){
  ctx.save();ctx.beginPath();ctx.rect(0,0,FIELD,HEIGHT);ctx.clip();
  for(const z of zones){const top=sy(Y(z.to)),bottom=sy(Y(z.from));if(bottom<0||top>HEIGHT)continue;ctx.fillStyle=z.color;ctx.fillRect(0,top,FIELD,bottom-top);ctx.fillStyle='#ffffff22';ctx.fillRect(35,top,FIELD-70,bottom-top);
    if(z.type==='safe'||z.type==='goal'){
      for(let y=Math.ceil((camera+Math.max(top,0))/44)*44;y<Math.min(Y(z.from),camera+HEIGHT);y+=44)for(let x=55;x<FIELD;x+=55)if((x+y)%3<2)flower(x+(y%17),sy(y));
      if(z.type==='safe'){const mid=sy((Y(z.from)+Y(z.to))/2);rounded(52,mid-30,232,59,18,'#fffdf0e6');text(z.name+' 🌿',168,mid-7,18);text(z.from===0?'위쪽으로 출발해요 ↑':'잠깐 쉬어 가도 괜찮아요',168,mid+16,11,'#83906d');}
    }else if(z.type==='bottle'){
      for(let y=Y(7);y>Y(34);y-=110)for(let x=78;x<FIELD;x+=125){ellipse(x+(Math.floor(y)%30),sy(y),23,8,'#d9c59722');text('✦',x+30,sy(y)+34,12,'#c6b98d');}
    }else if(z.type==='maze'){
      ctx.strokeStyle='#d9ceaa44';ctx.lineWidth=1;for(let y=Y(40);y>Y(59);y-=40){ctx.beginPath();ctx.moveTo(28,sy(y));ctx.lineTo(FIELD-28,sy(y));ctx.stroke();}
      walls.forEach((wall,i)=>{if(sy(wall.y+wall.h)>-50&&sy(wall.y)<HEIGHT+50)drawMazeWall(wall,false,i);});
      movingWalls.forEach((wall,i)=>{const pose=wallPose(wall);if(sy(pose.y+pose.h)>-50&&sy(pose.y)<HEIGHT+50)drawMazeWall(pose,true,i);});
      text('입구 ↑',maze.left+(maze.entry%maze.cols+.5)*maze.cell,sy(maze.top+maze.rows*maze.cell)+48,15,'#a4936a');
      text('출구 ↑',maze.left+(maze.exit+.5)*maze.cell,sy(maze.top)-43,15,'#a4936a');
    }else if(z.type==='stroller'){
      for(let lane=0;lane<9;lane++){const y=sy(Y(88+lane*3));ctx.strokeStyle='#b7c5c455';ctx.lineWidth=2;ctx.setLineDash([15,18]);ctx.beginPath();ctx.moveTo(37,y+45);ctx.lineTo(FIELD-37,y+45);ctx.stroke();ctx.setLineDash([]);text(lane%2?'←':'→',54,y,20,'#a4b4ae');}
    }
    ctx.strokeStyle='#7d8f6633';ctx.lineWidth=2;ctx.setLineDash([5,7]);ctx.beginPath();ctx.moveTo(35,top);ctx.lineTo(FIELD-35,top);ctx.stroke();ctx.setLineDash([]);
    if(z.type!=='safe'&&z.type!=='goal'){rounded(FIELD/2-135,bottom-39,270,29,10,'#fffdf0d9');text(z.name+' ↑',FIELD/2,bottom-24,14,'#7b755c');}
  }
  for(let y=Math.floor(camera/36)*36;y<camera+HEIGHT+36;y+=36)for(const x of [18,FIELD-18])rounded(x-3,sy(y),6,24,2,'#9ba885');
  for(const x of [18,FIELD-18]){ctx.strokeStyle='#9ba885';ctx.lineWidth=3;ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,HEIGHT);ctx.stroke();}
  for(const b of bottles)if(sy(b.y)>-70&&sy(b.y)<HEIGHT+70)bottle(b);
  for(const s of strollers)if(sy(s.y)>-65&&sy(s.y)<HEIGHT+65)stroller(s);
  const gy=sy(goal.y);ellipse(goal.x,gy+47,74,16,'#dca7ad30');circle(goal.x,gy+5,54,'#fff1de');
  character('mom',goal.x+(won?29:0),gy,30,{happy:won});text(won?'💕':'엄마',goal.x,gy-54,won?30:17,'#a07276');
  if(won){character('hero',player.x,sy(player.y),24,{happy:true});text('♥',goal.x,gy+28,19,'#c77982');}
  else if(player.flash<=0||Math.floor(visualTime*12)%2)character('hero',player.x,sy(player.y),player.r,{walking:running&&player.walking});
  ctx.restore();
}
function draw(dt){visualTime+=dt;ctx.clearRect(0,0,WIDTH,HEIGHT);landscape();
  if(won)for(let i=0;i<8;i++){const t=(visualTime*.22+i*.15)%1;text('♥',goal.x+Math.sin(i*7)*90,170-t*150,17+i%3*5,'#d69ba3');}
  for(const p of particles){p.x+=p.vx*dt;p.y+=p.vy*dt;p.vy+=90*dt;p.life-=dt;ctx.save();ctx.globalAlpha=Math.min(1,Math.max(0,p.life));ctx.translate(p.x,p.y);ctx.rotate(p.y*.025);ctx.fillStyle=p.color;ctx.fillRect(-3,-3,6,10);ctx.restore();}particles=particles.filter(p=>p.life>0&&p.y<HEIGHT);}
function frame(now){const dt=clamp((now-last)/1000||0,0,.04);last=now;update(dt);draw(dt);requestAnimationFrame(frame);}
const valid=['ArrowUp','ArrowDown','ArrowLeft','ArrowRight','w','a','s','d'];
window.addEventListener('keydown',e=>{const key=e.key.length===1?e.key.toLowerCase():e.key;if(valid.includes(key)&&e.target.tagName!=='INPUT'){e.preventDefault();if(running)keys.add(key);}});
window.addEventListener('keyup',e=>keys.delete(e.key.length===1?e.key.toLowerCase():e.key));
window.addEventListener('blur',pauseGame);
document.addEventListener('visibilitychange',()=>{if(document.hidden)pauseGame();});
document.querySelectorAll('[data-key]').forEach(b=>{
  b.onpointerdown=e=>{if(!running||controlMode!=='buttons'||(e.pointerType==='mouse'&&e.button!==0))return;e.preventDefault();b.setPointerCapture(e.pointerId);heldButtons.set(e.pointerId,b.dataset.key);};
  b.onpointerup=b.onpointercancel=b.onlostpointercapture=e=>heldButtons.delete(e.pointerId);
});
function moveStick(e){
  const dx=e.clientX-gesture.originX,dy=e.clientY-gesture.originY,len=Math.hypot(dx,dy);
  const factor=len?Math.min(len,gesture.radius)/len:0;
  gesture.x=gesture.originX+dx*factor;gesture.y=gesture.originY+dy*factor;
  ui.joystick.style.setProperty('--stick-x',dx*factor+'px');ui.joystick.style.setProperty('--stick-y',dy*factor+'px');
}
ui.joystick.onpointerdown=e=>{
  if(!running||controlMode!=='drag'||gesture||(e.pointerType==='mouse'&&e.button!==0))return;
  const r=ui.joystick.getBoundingClientRect();
  const x=r.left+r.width/2,y=r.top+r.height/2;
  e.preventDefault();ui.joystick.setPointerCapture(e.pointerId);
  gesture={id:e.pointerId,originX:x,originY:y,x,y,radius:Math.min(36,r.height*3/11)};moveStick(e);
};
ui.joystick.onpointermove=e=>{if(gesture?.id!==e.pointerId)return;e.preventDefault();moveStick(e);};
ui.joystick.onpointerup=ui.joystick.onpointercancel=ui.joystick.onlostpointercapture=e=>{
  if(gesture?.id!==e.pointerId)return;
  clearControls();
};
const photoVersions={hero:0,mom:0},photoKey=name=>'gotomom.photo.'+name;
function decodePhoto(src){return new Promise((resolve,reject)=>{const img=new Image();img.onload=()=>img.naturalWidth&&img.naturalHeight?resolve(img):reject(Error('empty image'));img.onerror=()=>reject(Error('unsupported image'));img.src=src;});}
async function loadPhoto(name,dataUrl,version=++photoVersions[name]){
  const img=await decodePhoto(dataUrl);if(version!==photoVersions[name])return null;
  const preview=new Image();preview.alt=name==='hero'?'주인공 사진':'엄마 사진';preview.src=dataUrl;
  faces[name]=img;document.querySelector('#'+name+'Preview').replaceChildren(preview);return img;
}
async function selectPhoto(name,file){
  const version=++photoVersions[name];ui.photoStatus.textContent='사진을 준비하고 있어요…';
  try{
    const original=await new Promise((resolve,reject)=>{const reader=new FileReader();reader.onload=()=>resolve(reader.result);reader.onerror=reject;reader.readAsDataURL(file);});
    const img=await decodePhoto(original),scale=Math.min(1,512/Math.max(img.naturalWidth,img.naturalHeight));
    const copy=document.createElement('canvas');copy.width=Math.max(1,Math.round(img.naturalWidth*scale));copy.height=Math.max(1,Math.round(img.naturalHeight*scale));
    const g=copy.getContext('2d');g.fillStyle='#fffaf0';g.fillRect(0,0,copy.width,copy.height);g.drawImage(img,0,0,copy.width,copy.height);
    const data=copy.toDataURL('image/jpeg',.9),loaded=await loadPhoto(name,data,version);if(!loaded)return false;
    try{localStorage.setItem(photoKey(name),data);ui.photoStatus.textContent='사진이 캐릭터에 적용됐어요. 다음에도 이 기기에서 그대로 보여요.';}
    catch{ui.photoStatus.textContent='사진이 적용됐어요. 이 브라우저에서는 저장이 제한되어 다음에 다시 골라 주세요.';}
    return true;
  }catch{if(version===photoVersions[name])ui.photoStatus.textContent='사진을 읽지 못했어요. JPG·PNG 사진을 다시 골라 주세요.';return false;}
}
async function restorePhotos(){
  await Promise.all(['hero','mom'].map(async name=>{
    try{const saved=localStorage.getItem(photoKey(name));if(saved){const img=await loadPhoto(name,saved);if(img)ui.photoStatus.textContent='이 기기에 저장된 사진을 불러왔어요.';}}
    catch{ui.photoStatus.textContent='저장된 사진을 읽지 못했어요. 사진을 다시 골라 주세요.';}
  }));
}
for(const name of ['hero','mom'])document.querySelector('#'+name).onchange=async e=>{const file=e.target.files[0];if(file){pauseGame();await selectPhoto(name,file);}e.target.value='';};
document.querySelectorAll('[data-remove-photo]').forEach(button=>button.onclick=()=>{
  const name=button.dataset.removePhoto;++photoVersions[name];faces[name]=null;
  document.querySelector('#'+name+'Preview').textContent=name==='hero'?'🧒':'👩';
  try{localStorage.removeItem(photoKey(name));}catch{}
  ui.photoStatus.textContent='사진을 지웠어요. 기본 캐릭터로 보여요.';
});
window.addEventListener('resize',fitCanvas);
if(typeof ResizeObserver!=='undefined')new ResizeObserver(fitCanvas).observe(ui.stage);
chooseMode(controlMode);reset();fitCanvas();restorePhotos();requestAnimationFrame(frame);
