// Exact arithmetic shared by the educational demos and their tests.
const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a;};
export class Q {
  constructor(n,d=1n){n=BigInt(n);d=BigInt(d);if(!d)throw Error('A denominator cannot be zero.');if(d<0n){n=-n;d=-d;}const g=gcd(n,d);this.n=n/g;this.d=d/g;}
  static of(x){return x instanceof Q?x:new Q(x);}
  static parse(text){text=String(text).trim();if(text.length>120||!/^[-+]?\d+(?:\/[-+]?\d+)?$/.test(text))throw Error('Use a whole number or a fraction, such as -2 or 3/5.');const [n,d='1']=text.split('/');return new Q(n,d);}
  add(b){b=Q.of(b);return new Q(this.n*b.d+b.n*this.d,this.d*b.d);}
  sub(b){return this.add(Q.of(b).neg());}
  mul(b){b=Q.of(b);return new Q(this.n*b.n,this.d*b.d);}
  div(b){b=Q.of(b);return new Q(this.n*b.d,this.d*b.n);}
  neg(){return new Q(-this.n,this.d);}
  abs(){return this.n<0n?this.neg():this;}
  cmp(b){b=Q.of(b);const v=this.n*b.d-b.n*this.d;return v<0n?-1:v>0n?1:0;}
  pow(n){if(!Number.isInteger(n)||n<0||n>128)throw Error('Choose a natural exponent at most 128.');return new Q(this.n**BigInt(n),this.d**BigInt(n));}
  number(){return Number(this.n)/Number(this.d);}
  toString(){return this.d===1n?String(this.n):`${this.n}/${this.d}`;}
}
const q=x=>Q.of(x),min=(a,b)=>a.cmp(b)<0?a:b,max=(a,b)=>a.cmp(b)>0?a:b;
function natural(n,lo,hi){if(!Number.isInteger(n)||n<lo||n>hi)throw Error(`Choose a whole number from ${lo} to ${hi}.`);return n;}
export function oddSquares(n){natural(n,0,12);const terms=Array.from({length:n},(_,i)=>2*i+1);return {terms,sum:terms.reduce((a,b)=>a+b,0),square:n*n};}
export function clockNext(state,modulus=3){natural(modulus,2,9);natural(state,0,modulus-1);return (state+1)%modulus;}
export function interval(lo,hi){lo=q(lo);hi=q(hi);if(lo.cmp(hi)>0)throw Error('Each lower endpoint must be at most its upper endpoint.');return [lo,hi];}
export function intervalOperation(left,right,operation,factor=q(1)){
  let result;if(operation==='add')result=[left[0].add(right[0]),left[1].add(right[1])];
  else if(operation==='subtract')result=[left[0].sub(right[1]),left[1].sub(right[0])];
  else if(operation==='scale'){factor=q(factor);const a=left[0].mul(factor),b=left[1].mul(factor);result=[min(a,b),max(a,b)];}
  else throw Error('Unknown interval operation.');
  return {bounds:result,width:result[1].sub(result[0]),radius:result[1].sub(result[0]).div(2)};
}
export function gridExample(count,width){natural(count,1,16);width=q(width);if(width.cmp(0)<0||width.cmp(2)>0)throw Error('Choose a full interval width from zero to two.');
  const samples=Array.from({length:count+1},(_,i)=>{const x=new Q(i,count),value=q(1).sub(x.sub(new Q(7,16)).abs().mul(4));return {x,value,lo:value.sub(width.div(2)),hi:value.add(width.div(2))};});
  return {samples,first:samples.findIndex(s=>s.lo.cmp(0)>0),margin:q(1).cmp(new Q(4,count).add(width))>0};
}
export function primePower(value){natural(value,2,256);for(let p=2;p<=value;p++){let prime=true;for(let d=2;d*d<=p;d++)if(p%d===0){prime=false;break;}if(!prime)continue;let k=0,n=value;while(n%p===0){n/=p;k++;}if(n===1)return {base:p,exponent:k};}return null;}
export function oneSided(values){values=values.map(q);if(values.length!==3)throw Error('This example uses three real values.');const oscillating=values[0].sub(values[1]).add(values[2]),plain=values.reduce((s,x)=>s.add(x),q(0)),budget=values.reduce((s,x)=>s.add(max(x,q(0)).mul(2)),q(0));return {oscillating,plain,combined:oscillating.abs().add(plain),budget};}
export function expBand(x,n){natural(x,0,4);natural(n,0,18);let term=q(1),sum=q(1);for(let k=1;k<=n;k++){term=term.mul(x).div(k);sum=sum.add(term);}const next=term.mul(x).div(n+1),upper=sum.add(next.mul(2));return {lower:sum,upper,width:upper.sub(sum),valid:2*x<=n+2,reciprocal:[q(1).div(upper),q(1).div(sum)]};}
export function complexMultiply(a,b){return [a[0].mul(b[0]).sub(a[1].mul(b[1])),a[0].mul(b[1]).add(a[1].mul(b[0]))];}
export function phaseGrid(t,n){t=q(t);natural(n,1,32);if(t.abs().cmp(4)>0)throw Error('Choose an angle from -4 to 4.');const step=t.div(n),square=step.pow(2),den=q(4).add(square),rotation=[q(4).sub(square).div(den),step.mul(4).div(den)];let point=[q(1),q(0)];for(let i=0;i<n;i++)point=complexMultiply(point,rotation);return {point,normSquared:point[0].pow(2).add(point[1].pow(2)),bound:t.pow(2).mul(2).div(n),valid:t.abs().cmp(n)<=0};}
export function squareInterval(bounds){const a=bounds[0].pow(2),b=bounds[1].pow(2);return [bounds[0].cmp(0)<=0&&bounds[1].cmp(0)>=0?q(0):min(a,b),max(a,b)];}
export function boxDistance(sigma,height,box){const real=squareInterval([q(sigma).sub(box[1]),q(sigma).sub(box[0])]),imag=squareInterval([q(height).sub(box[3]),q(height).sub(box[2])]);return [real[0].add(imag[0]),real[1].add(imag[1])];}
export function circleExample(radiusSquared){radiusSquared=q(radiusSquared);const selected=boxDistance(2,1,[new Q(59,100),new Q(61,100),new Q(99,100),new Q(101,100)]),other=boxDistance(2,1,[new Q(59,100),new Q(61,100),new Q(-101,100),new Q(-99,100)]);return {selected,other,inside:selected[1].cmp(radiusSquared)<0,outside:other[0].cmp(radiusSquared)>0,passes:radiusSquared.cmp(0)>0&&selected[1].cmp(radiusSquared)<0&&other[0].cmp(radiusSquared)>0};}
export function windowWitness(start,address,lower){start=q(start);address=q(address);lower=q(lower);if(start.cmp(1)<=0)throw Error('Choose a window start greater than one.');return {aboveStart:address.cmp(start)>=0,belowEnd:address.cmp(0)>=0&&address.pow(2).cmp(start.pow(3))<=0,positiveLower:lower.cmp(0)>0};}
