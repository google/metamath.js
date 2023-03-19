include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cldil.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "wi.mm"
include "catm.mm"
include "wral.mm"
include "eqid.mm"
include "ltrnldil.mm"
include "ldilcnv.mm"
include "syldan.mm"
include "w3a.mm"
include "simp1.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2l.mm"
include "simp3l.mm"
include "ltrncnvel.mm"
include "syl112anc.mm"
include "simp2r.mm"
include "simp3r.mm"
include "ltrnu.mm"
include "syl3anc.mm"
include "cbs.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "3ad2ant1.mm"
include "atbase.mm"
include "syl.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "simp1ll.mm"
include "ltrncnvat.mm"
include "hlatjcom.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "wb.mm"
include "isltrn.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem ltrncnv
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  assume ltrncnv.h: |- H = ( LHyp ` K )
  assume ltrncnv.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> `' F e. T )

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
    #
    cF
    ccnv
    #
    cT
    wcel
    #
    @5
    cW
    cK
    cldil
    cfv
    cfv
    #
    wcel
    #
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
    vq
    cv
    #
    cW
    @10
    wbr
    wn
    #
    wa
    #
    @9
    @9
    @5
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
    @12
    @12
    @5
    cfv
    #
    @16
    co
    #
    cW
    @18
    co
    #
    wceq
    #
    wi
    #
    vq
    cK
    catm
    cfv
    #
    wral
    vp
    @25
    wral
    #
    @2
    @3
    cF
    @7
    wcel
    @8
    @7
    cT
    cF
    cH
    cK
    chlt
    cW
    ltrncnv.h
    @7
    eqid
    #
    ltrncnv.t
    ltrnldil
    @7
    cF
    cH
    cK
    cW
    ltrncnv.h
    @27
    ldilcnv
    syldan
    @4
    @24
    vp
    vq
    @25
    @25
    @4
    @9
    @25
    wcel
    #
    @12
    @25
    wcel
    #
    wa
    #
    @14
    @23
    @4
    @30
    @14
    w3a
    #
    @15
    @15
    cF
    cfv
    #
    @16
    co
    #
    cW
    @18
    co
    #
    @20
    @20
    cF
    cfv
    #
    @16
    co
    #
    cW
    @18
    co
    #
    @19
    @22
    @31
    @4
    @15
    @25
    wcel
    #
    @15
    cW
    @10
    wbr
    wn
    wa
    #
    @20
    @25
    wcel
    #
    @20
    cW
    @10
    wbr
    wn
    wa
    #
    @34
    @37
    wceq
    @4
    @30
    @14
    simp1
    @31
    @2
    @3
    @28
    @11
    @39
    @2
    @3
    @30
    @14
    simp1l
    #
    @2
    @3
    @30
    @14
    simp1r
    #
    @4
    @28
    @29
    @14
    simp2l
    #
    @4
    @30
    @11
    @13
    simp3l
    @25
    @9
    cT
    cF
    cH
    cK
    @10
    cW
    @10
    eqid
    #
    @25
    eqid
    #
    ltrncnv.h
    ltrncnv.t
    ltrncnvel
    syl112anc
    @31
    @2
    @3
    @29
    @13
    @41
    @42
    @43
    @4
    @28
    @29
    @14
    simp2r
    #
    @4
    @30
    @11
    @13
    simp3r
    @25
    @12
    cT
    cF
    cH
    cK
    @10
    cW
    @45
    @46
    ltrncnv.h
    ltrncnv.t
    ltrncnvel
    syl112anc
    @25
    @15
    @20
    cT
    cF
    cH
    @16
    cK
    @10
    @18
    chlt
    cW
    @45
    @16
    eqid
    #
    @18
    eqid
    #
    @46
    ltrncnv.h
    ltrncnv.t
    ltrnu
    syl3anc
    @31
    @33
    @17
    cW
    @18
    @31
    @33
    @15
    @9
    @16
    co
    #
    @17
    @31
    @32
    @9
    @15
    @16
    @31
    cK
    cbs
    cfv
    #
    @51
    cF
    wf1o
    #
    @9
    @51
    wcel
    #
    @32
    @9
    wceq
    @4
    @30
    @52
    @14
    @51
    cT
    cF
    cH
    cK
    chlt
    cW
    @51
    eqid
    #
    ltrncnv.h
    ltrncnv.t
    ltrn1o
    3ad2ant1
    #
    @31
    @28
    @53
    @44
    @25
    @51
    @9
    cK
    @54
    @46
    atbase
    syl
    @51
    @51
    @9
    cF
    f1ocnvfv2
    syl2anc
    oveq2d
    @31
    @0
    @38
    @28
    @50
    @17
    wceq
    @0
    @1
    @3
    @30
    @14
    simp1ll
    #
    @31
    @2
    @3
    @28
    @38
    @42
    @43
    @44
    @25
    @9
    cT
    cF
    cH
    cK
    @10
    cW
    @45
    @46
    ltrncnv.h
    ltrncnv.t
    ltrncnvat
    syl3anc
    @44
    @25
    @16
    cK
    @15
    @9
    @48
    @46
    hlatjcom
    syl3anc
    eqtrd
    oveq1d
    @31
    @36
    @21
    cW
    @18
    @31
    @36
    @20
    @12
    @16
    co
    #
    @21
    @31
    @35
    @12
    @20
    @16
    @31
    @52
    @12
    @51
    wcel
    #
    @35
    @12
    wceq
    @55
    @31
    @29
    @58
    @47
    @25
    @51
    @12
    cK
    @54
    @46
    atbase
    syl
    @51
    @51
    @12
    cF
    f1ocnvfv2
    syl2anc
    oveq2d
    @31
    @0
    @40
    @29
    @57
    @21
    wceq
    @56
    @31
    @2
    @3
    @29
    @40
    @42
    @43
    @47
    @25
    @12
    cT
    cF
    cH
    cK
    @10
    cW
    @45
    @46
    ltrncnv.h
    ltrncnv.t
    ltrncnvat
    syl3anc
    @47
    @25
    @16
    cK
    @20
    @12
    @48
    @46
    hlatjcom
    syl3anc
    eqtrd
    oveq1d
    3eqtr3d
    3exp
    ralrimivv
    @2
    @6
    @8
    @26
    wa
    wb
    @3
    @25
    chlt
    @7
    cT
    @5
    cH
    @16
    cK
    @10
    @18
    cW
    vq
    vp
    @45
    @48
    @49
    @46
    ltrncnv.h
    @27
    ltrncnv.t
    isltrn
    adantr
    mpbir2and
end
