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
include "crio.mm"
include "cmpt.mm"
include "simp2l2.mm"
include "simp2r.mm"
include "eqid.mm"
include "cdlemkuu.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2l.mm"
include "simp31.mm"
include "simp321.mm"
include "simp323.mm"
include "simp322.mm"
include "3jca.mm"
include "simp33.mm"
include "cdlemkuv2.mm"
include "syl313anc.mm"
include "eqtrd.mm"

theorem cdlemk31
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ b e. T /\ N e. T ) /\ G e. T ) /\ ( ( ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) /\ ( F =/= ( _I |` B ) /\ b =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( b Y G ) ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( ( S ` b ) ` P ) .\/ ( R ` ( G o. `' b ) ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    #
    wa
    #
    cF
    cT
    wcel
    #
    vb
    cv
    #
    cT
    wcel
    #
    cN
    cT
    wcel
    #
    w3a
    #
    cG
    cT
    wcel
    #
    wa
    #
    @5
    cR
    cfv
    #
    @1
    wne
    @11
    cG
    cR
    cfv
    #
    wne
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    @5
    @14
    wne
    #
    cG
    @14
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
    @5
    cG
    cY
    co
    #
    cfv
    cP
    cG
    ve
    cT
    cP
    vj
    cv
    cfv
    cP
    ve
    cv
    #
    cR
    cfv
    c.or
    co
    cP
    @5
    cS
    cfv
    #
    cfv
    #
    @23
    @5
    ccnv
    #
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    vj
    cT
    crio
    cmpt
    #
    cfv
    #
    cfv
    #
    cP
    @12
    c.or
    co
    @25
    cG
    @26
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    @21
    cP
    @22
    @28
    @21
    @6
    @9
    @22
    @28
    wceq
    @4
    @6
    @7
    @9
    @3
    @20
    simp2l2
    @3
    @8
    @9
    @20
    simp2r
    #
    cA
    cB
    @5
    cP
    @24
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
    @27
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
    @24
    eqid
    #
    @27
    eqid
    #
    cdlemkuu
    syl2anc
    fveq1d
    @21
    @0
    @2
    @9
    @8
    @13
    @15
    @17
    @16
    w3a
    @19
    @29
    @30
    wceq
    @0
    @2
    @10
    @20
    simp1l
    @0
    @2
    @10
    @20
    simp1r
    @31
    @3
    @8
    @9
    @20
    simp2l
    @3
    @10
    @13
    @18
    @19
    simp31
    @21
    @15
    @17
    @16
    @15
    @16
    @17
    @13
    @19
    @3
    @10
    simp321
    @15
    @16
    @17
    @13
    @19
    @3
    @10
    simp323
    @15
    @16
    @17
    @13
    @19
    @3
    @10
    simp322
    3jca
    @3
    @10
    @13
    @18
    @19
    simp33
    cA
    cB
    @5
    cP
    cR
    cS
    cT
    @27
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
    @24
    cW
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.m
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.s
    @32
    @33
    cdlemkuv2
    syl313anc
    eqtrd
end
