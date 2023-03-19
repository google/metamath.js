include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "simp31.mm"
include "simp32l.mm"
include "simp331.mm"
include "simp32r.mm"
include "neeqtrrd.mm"
include "jca.mm"
include "simp33.mm"
include "3jca.mm"
include "cdlemk23-3.mm"
include "syld3an3.mm"

theorem cdlemk24-3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
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
  let vd: setvar d
  let cQ: class Q
  let vb: setvar b
  assume cdlemk3.b: |- B = ( Base ` K )
  assume cdlemk3.l: |- .<_ = ( le ` K )
  assume cdlemk3.j: |- .\/ = ( join ` K )
  assume cdlemk3.m: |- ./\ = ( meet ` K )
  assume cdlemk3.a: |- A = ( Atoms ` K )
  assume cdlemk3.h: |- H = ( LHyp ` K )
  assume cdlemk3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk3.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk3.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk3.u1: |- Y = ( d e. T , e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` d ) ` P ) .\/ ( R ` ( e o. `' d ) ) ) ) ) )

  disjoint d e
  disjoint d f
  disjoint d i
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint ./\ e
  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ d
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint d j
  disjoint D d
  disjoint e j
  disjoint D e
  disjoint f j
  disjoint D f
  disjoint i j
  disjoint D i
  disjoint D j
  disjoint F f
  disjoint F i
  disjoint G d
  disjoint G e
  disjoint G j
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint W d
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint ./\ j
  disjoint .<_ j
  disjoint .\/ j
  disjoint A j
  disjoint F j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint P j
  disjoint R j
  disjoint S d
  disjoint S e
  disjoint S j
  disjoint T j
  disjoint W j
  disjoint F d
  disjoint F e
  disjoint .<_ e
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C i
  disjoint C j
  disjoint G f
  disjoint G i
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint i x
  disjoint j x
  disjoint Q d
  disjoint Q e
  disjoint b f
  disjoint b i
  disjoint b d
  disjoint b e
  disjoint b j
  disjoint S b
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( G e. T /\ C e. T /\ x e. T ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( ( R ` F ) = ( R ` N ) /\ F =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( G =/= ( _I |` B ) /\ C =/= ( _I |` B ) /\ x =/= ( _I |` B ) ) ) /\ ( ( ( R ` G ) =/= ( R ` C ) /\ ( R ` C ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` F ) ) /\ ( ( R ` G ) =/= ( R ` D ) /\ ( R ` C ) = ( R ` D ) ) /\ ( ( R ` x ) =/= ( R ` D ) /\ ( R ` x ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` x ) ) ) ) -> ( ( D Y G ) ` P ) = ( ( C Y G ) ` P ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    cD
    cT
    wcel
    cN
    cT
    wcel
    w3a
    cG
    cT
    wcel
    cC
    cT
    wcel
    vx
    cv
    #
    cT
    wcel
    w3a
    w3a
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    cF
    cid
    cB
    cres
    #
    wne
    cD
    @3
    wne
    w3a
    cG
    @3
    wne
    cC
    @3
    wne
    @0
    @3
    wne
    w3a
    w3a
    #
    cG
    cR
    cfv
    #
    cC
    cR
    cfv
    #
    wne
    @6
    @2
    wne
    cD
    cR
    cfv
    #
    @2
    wne
    w3a
    #
    @5
    @7
    wne
    #
    @6
    @7
    wceq
    #
    wa
    #
    @0
    cR
    cfv
    #
    @7
    wne
    #
    @12
    @2
    wne
    #
    @5
    @12
    wne
    #
    w3a
    #
    w3a
    #
    @8
    @9
    @12
    @6
    wne
    #
    wa
    #
    @16
    w3a
    cP
    cD
    cG
    cY
    co
    cfv
    cP
    cC
    cG
    cY
    co
    cfv
    wceq
    @1
    @4
    @17
    w3a
    #
    @8
    @19
    @16
    @1
    @4
    @8
    @11
    @16
    simp31
    @20
    @9
    @18
    @9
    @10
    @8
    @16
    @1
    @4
    simp32l
    @20
    @12
    @7
    @6
    @13
    @14
    @15
    @8
    @11
    @1
    @4
    simp331
    @9
    @10
    @8
    @16
    @1
    @4
    simp32r
    neeqtrrd
    jca
    @1
    @4
    @8
    @11
    @16
    simp33
    3jca
    vx
    cA
    cB
    cC
    cD
    cP
    cR
    cS
    cT
    ve
    vf
    vi
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cY
    vd
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.m
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.s
    cdlemk3.u1
    cdlemk23-3
    syld3an3
end
