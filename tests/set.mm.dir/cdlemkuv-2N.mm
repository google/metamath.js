include "cdlemksv.mm"

theorem cdlemkuv-2N
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let vd: setvar d
  assume cdlemk2.b: |- B = ( Base ` K )
  assume cdlemk2.l: |- .<_ = ( le ` K )
  assume cdlemk2.j: |- .\/ = ( join ` K )
  assume cdlemk2.m: |- ./\ = ( meet ` K )
  assume cdlemk2.a: |- A = ( Atoms ` K )
  assume cdlemk2.h: |- H = ( LHyp ` K )
  assume cdlemk2.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk2.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk2.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk2.q: |- Q = ( S ` C )
  assume cdlemk2.v: |- V = ( d e. T |-> ( iota_ k e. T ( k ` P ) = ( ( P .\/ ( R ` d ) ) ./\ ( ( Q ` P ) .\/ ( R ` ( d o. `' C ) ) ) ) ) )

  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint C f
  disjoint C i
  disjoint F f
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P f
  disjoint P i
  disjoint R f
  disjoint R i
  disjoint T f
  disjoint T i
  disjoint W f
  disjoint W i
  disjoint ./\ d
  disjoint .\/ d
  disjoint C d
  disjoint d k
  disjoint G d
  disjoint G k
  disjoint Q d
  disjoint P d
  disjoint R d
  disjoint T d
  disjoint W d
  assert |- ( G e. T -> ( V ` G ) = ( iota_ k e. T ( k ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( Q ` P ) .\/ ( R ` ( G o. `' C ) ) ) ) ) )

  proof
    cA
    cB
    cP
    cR
    cV
    cT
    vd
    vk
    cC
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cQ
    cW
    cdlemk2.b
    cdlemk2.l
    cdlemk2.j
    cdlemk2.a
    cdlemk2.h
    cdlemk2.t
    cdlemk2.r
    cdlemk2.m
    cdlemk2.v
    cdlemksv
end
