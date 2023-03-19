include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "w3a.mm"
include "wne.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "cdlemk31.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp31l.mm"
include "simp321.mm"
include "simp322.mm"
include "jca.mm"
include "simp33.mm"
include "cdlemk30.mm"
include "syl113anc.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem cdlemk32
  let cA: class A
  let cB: class B
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
  let vb: setvar b
  let vd: setvar d
  let cD: class D
  let cQ: class Q
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
  disjoint e j
  disjoint f j
  disjoint i j
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
  disjoint b f
  disjoint b i
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
  disjoint b d
  disjoint S d
  disjoint b e
  disjoint S e
  disjoint b j
  disjoint S j
  disjoint S b
  disjoint T j
  disjoint W j
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint Q d
  disjoint Q e
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ b e. T /\ N e. T ) /\ G e. T ) /\ ( ( ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) /\ ( F =/= ( _I |` B ) /\ b =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( b Y G ) ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) ) .\/ ( R ` ( G o. `' b ) ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    wa
    #
    cF
    cT
    wcel
    vb
    cv
    #
    cT
    wcel
    cN
    cT
    wcel
    w3a
    #
    cG
    cT
    wcel
    #
    wa
    #
    @2
    cR
    cfv
    #
    @0
    wne
    #
    @6
    cG
    cR
    cfv
    #
    wne
    #
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    @2
    @11
    wne
    #
    cG
    @11
    wne
    #
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
    #
    w3a
    #
    w3a
    #
    cP
    @2
    cG
    cY
    co
    cfv
    cP
    @8
    c.or
    co
    #
    cP
    @2
    cS
    cfv
    cfv
    #
    cG
    @2
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    @19
    cP
    @6
    c.or
    co
    cP
    cN
    cfv
    @2
    cF
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    @21
    c.or
    co
    #
    c.an
    co
    cA
    cB
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
    vb
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
    cdlemk31
    @18
    @22
    @24
    @19
    c.an
    @18
    @20
    @23
    @21
    c.or
    @18
    @1
    @3
    @7
    @12
    @13
    wa
    @16
    @20
    @23
    wceq
    @1
    @5
    @17
    simp1
    @1
    @3
    @4
    @17
    simp2l
    @7
    @9
    @15
    @16
    @1
    @5
    simp31l
    @18
    @12
    @13
    @12
    @13
    @14
    @10
    @16
    @1
    @5
    simp321
    @12
    @13
    @14
    @10
    @16
    @1
    @5
    simp322
    jca
    @1
    @5
    @10
    @15
    @16
    simp33
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    vb
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.m
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.s
    cdlemk30
    syl113anc
    oveq1d
    oveq2d
    eqtrd
end
