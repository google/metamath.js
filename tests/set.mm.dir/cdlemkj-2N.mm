include "cdlemkj.mm"

theorem cdlemkj-2N
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
  let cW: class W
  let cY: class Y
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
  assume cdlemk.y: |- Y = ( iota_ k e. T ( k ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( Q ` P ) .\/ ( R ` ( G o. `' C ) ) ) ) )

  disjoint ./\ k
  disjoint .<_ k
  disjoint .\/ k
  disjoint A k
  disjoint C k
  disjoint F k
  disjoint H k
  disjoint K k
  disjoint N k
  disjoint Q k
  disjoint P k
  disjoint R k
  disjoint T k
  disjoint W k
  disjoint G k
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) /\ G e. T ) /\ ( F e. T /\ C e. T /\ N e. T ) /\ ( ( ( R ` C ) =/= ( R ` F ) /\ ( R ` C ) =/= ( R ` G ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> Y e. T )

  proof
    cA
    cB
    cC
    cP
    cR
    cS
    cT
    vf
    vi
    vk
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cQ
    cW
    cY
    cdlemk2.b
    cdlemk2.l
    cdlemk2.j
    cdlemk2.m
    cdlemk2.a
    cdlemk2.h
    cdlemk2.t
    cdlemk2.r
    cdlemk2.s
    cdlemk2.q
    cdlemk.y
    cdlemkj
end
