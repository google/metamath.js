include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cp0.mm"
include "wo.mm"
include "w3a.mm"
include "catm.mm"
include "cops.mm"
include "cbs.mm"
include "simpl1l.mm"
include "hlop.mm"
include "syl.mm"
include "simpl1.mm"
include "simpl2r.mm"
include "eqid.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "simpr.mm"
include "simpl3.mm"
include "leat.mm"
include "syl31anc.mm"
include "simp3.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "wb.mm"
include "ople0.mm"
include "mpbid.mm"
include "olcd.mm"
include "simp1.mm"
include "simp2l.mm"
include "trlator0.mm"
include "mpjaodan.mm"
include "3expa.mm"
include "eqcom.mm"
include "cdlemk.mm"
include "sylan2b.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "tendo0cl.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "tendo02.mm"
include "trlid0b.mm"
include "adantrl.mm"
include "biimpar.mm"
include "eqtr4d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "jaodan.mm"
include "syldan.mm"
include "3impa.mm"

theorem tendoex
  let vu: setvar u
  let cR: class R
  let cT: class T
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let vh: setvar h
  assume tendoex.l: |- .<_ = ( le ` K )
  assume tendoex.h: |- H = ( LHyp ` K )
  assume tendoex.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoex.r: |- R = ( ( trL ` K ) ` W )
  assume tendoex.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint E u
  disjoint F u
  disjoint K u
  disjoint N u
  disjoint R u
  disjoint T u
  disjoint W u
  disjoint H h
  disjoint h u
  disjoint K h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T ) /\ ( R ` N ) .<_ ( R ` F ) ) -> E. u e. E ( u ` F ) = N )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    cN
    cT
    wcel
    #
    wa
    #
    cN
    cR
    cfv
    #
    cF
    cR
    cfv
    #
    c.le
    wbr
    #
    cF
    vu
    cv
    #
    cfv
    #
    cN
    wceq
    #
    vu
    cE
    wrex
    #
    @2
    @5
    wa
    #
    @8
    @6
    @7
    wceq
    #
    @6
    cK
    cp0
    cfv
    #
    wceq
    #
    wo
    #
    @12
    @2
    @5
    @8
    @17
    @2
    @5
    @8
    w3a
    #
    @7
    cK
    catm
    cfv
    #
    wcel
    #
    @17
    @7
    @15
    wceq
    #
    @18
    @20
    wa
    #
    cK
    cops
    wcel
    #
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @20
    @8
    @17
    @22
    @0
    @23
    @0
    @1
    @5
    @8
    @20
    simpl1l
    cK
    hlop
    #
    syl
    @22
    @2
    @4
    @25
    @2
    @5
    @8
    @20
    simpl1
    @3
    @4
    @2
    @8
    @20
    simpl2r
    @24
    cR
    cT
    cN
    cH
    cK
    cW
    @24
    eqid
    #
    tendoex.h
    tendoex.t
    tendoex.r
    trlcl
    #
    syl2anc
    @18
    @20
    simpr
    @2
    @5
    @8
    @20
    simpl3
    @19
    @24
    @7
    cK
    c.le
    @6
    @15
    @27
    tendoex.l
    @15
    eqid
    #
    @19
    eqid
    #
    leat
    syl31anc
    @18
    @21
    wa
    #
    @16
    @14
    @31
    @6
    @15
    c.le
    wbr
    #
    @16
    @18
    @21
    @32
    @18
    @8
    @21
    @32
    @2
    @5
    @8
    simp3
    @7
    @15
    @6
    c.le
    breq2
    syl5ibcom
    imp
    @31
    @23
    @25
    @32
    @16
    wb
    @31
    @0
    @23
    @0
    @1
    @5
    @8
    @21
    simpl1l
    @26
    syl
    @31
    @2
    @4
    @25
    @2
    @5
    @8
    @21
    simpl1
    @3
    @4
    @2
    @8
    @21
    simpl2r
    @28
    syl2anc
    @24
    cK
    c.le
    @6
    @15
    @27
    tendoex.l
    @29
    ople0
    syl2anc
    mpbid
    olcd
    @18
    @2
    @3
    @20
    @21
    wo
    @2
    @5
    @8
    simp1
    @2
    @3
    @4
    @8
    simp2l
    @19
    cR
    cT
    cF
    cH
    cK
    cW
    @15
    @29
    @30
    tendoex.h
    tendoex.t
    tendoex.r
    trlator0
    syl2anc
    mpjaodan
    3expa
    @13
    @14
    @12
    @16
    @14
    @13
    @7
    @6
    wceq
    #
    @12
    @6
    @7
    eqcom
    @2
    @5
    @33
    @12
    vu
    cR
    cT
    cE
    cF
    cH
    cK
    cN
    cW
    tendoex.h
    tendoex.t
    tendoex.r
    tendoex.e
    cdlemk
    3expa
    sylan2b
    @13
    @16
    wa
    #
    vh
    cT
    cid
    @24
    cres
    #
    cmpt
    #
    cE
    wcel
    #
    cF
    @36
    cfv
    #
    cN
    wceq
    #
    @12
    @2
    @37
    @5
    @16
    @24
    cT
    vh
    cE
    cH
    cK
    @36
    cW
    @27
    tendoex.h
    tendoex.t
    tendoex.e
    @36
    eqid
    #
    tendo0cl
    ad2antrr
    @34
    @38
    @35
    cN
    @34
    @3
    @38
    @35
    wceq
    @2
    @3
    @4
    @16
    simplrl
    @24
    cT
    vh
    cF
    cK
    @36
    @40
    @27
    tendo02
    syl
    @13
    cN
    @35
    wceq
    #
    @16
    @2
    @4
    @41
    @16
    wb
    @3
    @24
    cR
    cT
    cN
    cH
    cK
    cW
    @15
    @27
    @29
    tendoex.h
    tendoex.t
    tendoex.r
    trlid0b
    adantrl
    biimpar
    eqtr4d
    @11
    @39
    vu
    @36
    cE
    @9
    @36
    wceq
    @10
    @38
    cN
    cF
    @9
    @36
    fveq1
    eqeq1d
    rspcev
    syl2anc
    jaodan
    syldan
    3impa
end
