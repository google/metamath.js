include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "wn.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "cdlemf2.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3ll.mm"
include "simp2r.mm"
include "simp3lr.mm"
include "cdleme50ex.mm"
include "syl122anc.mm"
include "wi.mm"
include "simp3r.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "simp11.mm"
include "simp3l.mm"
include "simp13l.mm"
include "simp2ll.mm"
include "trlval2.mm"
include "syl112anc.mm"
include "3eqtr4d.mm"
include "3exp.mm"
include "3expia.mm"
include "3imp.mm"
include "expd.mm"
include "reximdvai.mm"
include "mpd.mm"
include "rexlimdvv.mm"

theorem cdlemf
  let cA: class A
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  assume cdlemf.l: |- .<_ = ( le ` K )
  assume cdlemf.a: |- A = ( Atoms ` K )
  assume cdlemf.h: |- H = ( LHyp ` K )
  assume cdlemf.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemf.r: |- R = ( ( trL ` K ) ` W )

  disjoint A f
  disjoint H f
  disjoint K f
  disjoint .<_ f
  disjoint T f
  disjoint U f
  disjoint W f
  disjoint f p
  disjoint f q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint H p
  disjoint H q
  disjoint K p
  disjoint K q
  disjoint .<_ p
  disjoint .<_ q
  disjoint R p
  disjoint R q
  disjoint T p
  disjoint T q
  disjoint U p
  disjoint U q
  disjoint W p
  disjoint W q
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. A /\ U .<_ W ) ) -> E. f e. T ( R ` f ) = U )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cA
    wcel
    cU
    cW
    c.le
    wbr
    wa
    #
    wa
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cU
    @3
    @5
    cK
    cjn
    cfv
    #
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    vf
    cv
    #
    cR
    cfv
    #
    cU
    wceq
    #
    vf
    cT
    wrex
    #
    cA
    cU
    cH
    @8
    cK
    c.le
    @10
    cW
    vq
    vp
    cdlemf.l
    @8
    eqid
    #
    cdlemf.a
    cdlemf.h
    @10
    eqid
    #
    cdlemf2
    @2
    @13
    @17
    vp
    vq
    cA
    cA
    @2
    @3
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    @13
    @17
    @2
    @22
    @13
    w3a
    #
    @3
    @14
    cfv
    #
    @5
    wceq
    #
    vf
    cT
    wrex
    #
    @17
    @23
    @0
    @20
    @4
    @21
    @6
    @26
    @0
    @1
    @22
    @13
    simp1l
    @2
    @20
    @21
    @13
    simp2l
    @4
    @6
    @12
    @2
    @22
    simp3ll
    @2
    @20
    @21
    @13
    simp2r
    @4
    @6
    @12
    @2
    @22
    simp3lr
    cA
    @3
    @5
    cT
    vf
    cH
    cK
    c.le
    cW
    cdlemf.l
    cdlemf.a
    cdlemf.h
    cdlemf.t
    cdleme50ex
    syl122anc
    @23
    @25
    @16
    vf
    cT
    @23
    @14
    cT
    wcel
    #
    @25
    @16
    @2
    @22
    @13
    @27
    @25
    wa
    #
    @16
    wi
    #
    @0
    @1
    @22
    @13
    @29
    wi
    @0
    @1
    @22
    w3a
    #
    @13
    @28
    @16
    @30
    @13
    @28
    w3a
    #
    @3
    @24
    @8
    co
    #
    cW
    @10
    co
    #
    @11
    @15
    cU
    @31
    @32
    @9
    cW
    @10
    @31
    @24
    @5
    @3
    @8
    @30
    @13
    @27
    @25
    simp3r
    oveq2d
    oveq1d
    @31
    @0
    @27
    @20
    @4
    @15
    @33
    wceq
    @0
    @1
    @22
    @13
    @28
    simp11
    @30
    @13
    @27
    @25
    simp3l
    @20
    @21
    @0
    @1
    @13
    @28
    simp13l
    @4
    @6
    @12
    @30
    @28
    simp2ll
    cA
    @3
    cR
    cT
    @14
    cH
    @8
    cK
    c.le
    @10
    cW
    cdlemf.l
    @18
    @19
    cdlemf.a
    cdlemf.h
    cdlemf.t
    cdlemf.r
    trlval2
    syl112anc
    @30
    @7
    @12
    @28
    simp2r
    3eqtr4d
    3exp
    3expia
    3imp
    expd
    reximdvai
    mpd
    3exp
    rexlimdvv
    mpd
end
