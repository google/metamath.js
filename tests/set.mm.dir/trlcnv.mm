include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "ccnv.mm"
include "wceq.mm"
include "catm.mm"
include "wrex.mm"
include "eqid.mm"
include "lhpexnle.mm"
include "adantr.mm"
include "w3a.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "cbs.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "3adant3.mm"
include "simp3l.mm"
include "atbase.mm"
include "syl.mm"
include "f1ocnvfv1.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "simp1l.mm"
include "ltrnat.mm"
include "3adant3r.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simp1.mm"
include "ltrncnv.mm"
include "ltrnel.mm"
include "trlval2.mm"
include "3eqtr4d.mm"
include "3expa.mm"
include "rexlimddv.mm"

theorem trlcnv
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  assume trlcnv.h: |- H = ( LHyp ` K )
  assume trlcnv.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlcnv.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( R ` `' F ) = ( R ` F ) )

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
    wa
    vp
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    cF
    ccnv
    #
    cR
    cfv
    #
    cF
    cR
    cfv
    #
    wceq
    #
    vp
    cK
    catm
    cfv
    #
    @2
    @6
    vp
    @11
    wrex
    @3
    @11
    cH
    cK
    @5
    cW
    vp
    @5
    eqid
    #
    @11
    eqid
    #
    trlcnv.h
    lhpexnle
    adantr
    @2
    @3
    @4
    @11
    wcel
    #
    @6
    wa
    #
    @10
    @2
    @3
    @15
    w3a
    #
    @4
    cF
    cfv
    #
    @17
    @7
    cfv
    #
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
    @4
    @17
    @19
    co
    #
    cW
    @21
    co
    @8
    @9
    @16
    @20
    @23
    cW
    @21
    @16
    @20
    @17
    @4
    @19
    co
    #
    @23
    @16
    @18
    @4
    @17
    @19
    @16
    cK
    cbs
    cfv
    #
    @25
    cF
    wf1o
    #
    @4
    @25
    wcel
    #
    @18
    @4
    wceq
    @2
    @3
    @26
    @15
    @25
    cT
    cF
    cH
    cK
    chlt
    cW
    @25
    eqid
    #
    trlcnv.h
    trlcnv.t
    ltrn1o
    3adant3
    @16
    @14
    @27
    @2
    @3
    @14
    @6
    simp3l
    #
    @11
    @25
    @4
    cK
    @28
    @13
    atbase
    syl
    @25
    @25
    @4
    cF
    f1ocnvfv1
    syl2anc
    oveq2d
    @16
    @0
    @17
    @11
    wcel
    #
    @14
    @24
    @23
    wceq
    @0
    @1
    @3
    @15
    simp1l
    @2
    @3
    @14
    @30
    @6
    @11
    @4
    cT
    cF
    cH
    cK
    @5
    cW
    @12
    @13
    trlcnv.h
    trlcnv.t
    ltrnat
    3adant3r
    @29
    @11
    @19
    cK
    @17
    @4
    @19
    eqid
    #
    @13
    hlatjcom
    syl3anc
    eqtrd
    oveq1d
    @16
    @2
    @7
    cT
    wcel
    #
    @30
    @17
    cW
    @5
    wbr
    wn
    wa
    @8
    @22
    wceq
    @2
    @3
    @15
    simp1
    @2
    @3
    @32
    @15
    cT
    cF
    cH
    cK
    cW
    trlcnv.h
    trlcnv.t
    ltrncnv
    3adant3
    @11
    @4
    cT
    cF
    cH
    cK
    @5
    cW
    @12
    @13
    trlcnv.h
    trlcnv.t
    ltrnel
    @11
    @17
    cR
    cT
    @7
    cH
    @19
    cK
    @5
    @21
    cW
    @12
    @31
    @21
    eqid
    #
    @13
    trlcnv.h
    trlcnv.t
    trlcnv.r
    trlval2
    syl3anc
    @11
    @4
    cR
    cT
    cF
    cH
    @19
    cK
    @5
    @21
    cW
    @12
    @31
    @33
    @13
    trlcnv.h
    trlcnv.t
    trlcnv.r
    trlval2
    3eqtr4d
    3expa
    rexlimddv
end
