include "cogrp.mm"
include "wcel.mm"
include "coppg.mm"
include "cfv.mm"
include "carchi.mm"
include "w3a.mm"
include "c0g.mm"
include "cv.mm"
include "cplt.mm"
include "wbr.mm"
include "cple.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cabl.mm"
include "cmg.mm"
include "eqid.mm"
include "simpll1.mm"
include "simpll3.mm"
include "simplr.mm"
include "simprl.mm"
include "simp2.mm"
include "simp1rr.mm"
include "simp3.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "archiabllem1.mm"
include "adantllr.mm"
include "simpr.mm"
include "breq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "r19.29a.mm"
include "wn.mm"
include "cplusg.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simpl2.mm"
include "ralnex.mm"
include "sylibr.mm"
include "rexanali.mm"
include "imbi2i.mm"
include "imnan.mm"
include "bitri.mm"
include "ralbii.mm"
include "notbid.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvralv.mm"
include "r19.21bi.mm"
include "syl6ib.mm"
include "3impia.mm"
include "ctos.mm"
include "wb.mm"
include "comnd.mm"
include "simp1l1.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "omndtos.mm"
include "3syl.mm"
include "tltnle.mm"
include "bicomd.mm"
include "3com23.mm"
include "3expa.mm"
include "rexbidva.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "archiabllem2.mm"
include "pm2.61dan.mm"

theorem archiabl
  let cW: class W
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( W e. oGrp /\ ( oppG ` W ) e. oGrp /\ W e. Archi ) -> W e. Abel )

  proof
    cW
    cogrp
    wcel
    #
    cW
    coppg
    cfv
    cogrp
    wcel
    #
    cW
    carchi
    wcel
    #
    w3a
    #
    cW
    c0g
    cfv
    #
    vu
    cv
    #
    cW
    cplt
    cfv
    #
    wbr
    #
    @4
    vx
    cv
    #
    @6
    wbr
    #
    @5
    @8
    cW
    cple
    cfv
    #
    wbr
    #
    wi
    #
    vx
    cW
    cbs
    cfv
    #
    wral
    #
    wa
    #
    vu
    @13
    wrex
    #
    cW
    cabl
    wcel
    #
    @3
    @16
    wa
    #
    @4
    vv
    cv
    #
    @6
    wbr
    #
    @9
    @19
    @8
    @10
    wbr
    #
    wi
    #
    vx
    @13
    wral
    #
    wa
    #
    @17
    vv
    @13
    @3
    @19
    @13
    wcel
    #
    @24
    @17
    @16
    @3
    @25
    wa
    #
    @24
    wa
    #
    vy
    @13
    @6
    cW
    cmg
    cfv
    #
    @19
    @10
    cW
    @4
    @13
    eqid
    #
    @4
    eqid
    #
    @10
    eqid
    #
    @6
    eqid
    #
    @28
    eqid
    #
    @0
    @1
    @2
    @25
    @24
    simpll1
    @0
    @1
    @2
    @25
    @24
    simpll3
    @3
    @25
    @24
    simplr
    @26
    @20
    @23
    simprl
    @27
    vy
    cv
    #
    @13
    wcel
    #
    @4
    @34
    @6
    wbr
    #
    w3a
    @35
    @23
    @36
    @19
    @34
    @10
    wbr
    #
    @27
    @35
    @36
    simp2
    @20
    @23
    @26
    @35
    @36
    simp1rr
    @27
    @35
    @36
    simp3
    @22
    @36
    @37
    wi
    vx
    @34
    @13
    @8
    @34
    wceq
    #
    @9
    @36
    @21
    @37
    @8
    @34
    @4
    @6
    breq2
    #
    @8
    @34
    @19
    @10
    breq2
    #
    imbi12d
    rspcv
    syl3c
    archiabllem1
    adantllr
    @18
    @16
    @24
    vv
    @13
    wrex
    @3
    @16
    simpr
    @15
    @24
    vu
    vv
    @13
    @5
    @19
    wceq
    #
    @7
    @20
    @14
    @23
    @5
    @19
    @4
    @6
    breq2
    #
    @41
    @12
    @22
    vx
    @13
    @41
    @11
    @21
    @9
    @5
    @19
    @8
    @10
    breq1
    #
    imbi2d
    ralbidv
    anbi12d
    cbvrexv
    sylib
    r19.29a
    @3
    @16
    wn
    #
    wa
    #
    @13
    cW
    cplusg
    cfv
    #
    @6
    @28
    @10
    cW
    @4
    vv
    vy
    @29
    @30
    @31
    @32
    @33
    @0
    @1
    @2
    @44
    simpl1
    @0
    @1
    @2
    @44
    simpl3
    @46
    eqid
    @0
    @1
    @2
    @44
    simpl2
    @45
    @25
    @20
    w3a
    #
    @36
    @37
    wn
    #
    wa
    #
    vy
    @13
    wrex
    #
    @36
    @34
    @19
    @6
    wbr
    #
    wa
    #
    vy
    @13
    wrex
    #
    @45
    @25
    @20
    @50
    @45
    @25
    wa
    @20
    @9
    @21
    wn
    #
    wa
    #
    vx
    @13
    wrex
    #
    @50
    @45
    @20
    @56
    wi
    #
    vv
    @13
    @45
    @7
    @9
    @11
    wn
    #
    wa
    #
    vx
    @13
    wrex
    #
    wi
    #
    vu
    @13
    wral
    #
    @57
    vv
    @13
    wral
    @45
    @15
    wn
    #
    vu
    @13
    wral
    #
    @62
    @45
    @44
    @64
    @3
    @44
    simpr
    @15
    vu
    @13
    ralnex
    sylibr
    @61
    @63
    vu
    @13
    @61
    @7
    @14
    wn
    #
    wi
    @63
    @60
    @65
    @7
    @9
    @11
    vx
    @13
    rexanali
    imbi2i
    @7
    @14
    imnan
    bitri
    ralbii
    sylibr
    @61
    @57
    vu
    vv
    @13
    @41
    @7
    @20
    @60
    @56
    @42
    @41
    @59
    @55
    vx
    @13
    @41
    @58
    @54
    @9
    @41
    @11
    @21
    @43
    notbid
    anbi2d
    rexbidv
    imbi12d
    cbvralv
    sylib
    r19.21bi
    @55
    @49
    vx
    vy
    @13
    @38
    @9
    @36
    @54
    @48
    @39
    @38
    @21
    @37
    @40
    notbid
    anbi12d
    cbvrexv
    syl6ib
    3impia
    @47
    cW
    ctos
    wcel
    #
    @25
    @50
    @53
    wb
    @47
    @0
    cW
    comnd
    wcel
    #
    @66
    @0
    @1
    @2
    @44
    @25
    @20
    simp1l1
    @0
    cW
    cgrp
    wcel
    @67
    cW
    isogrp
    simprbi
    cW
    omndtos
    3syl
    @45
    @25
    @20
    simp2
    @66
    @25
    wa
    #
    @49
    @52
    vy
    @13
    @68
    @35
    wa
    @48
    @51
    @36
    @66
    @25
    @35
    @48
    @51
    wb
    #
    @66
    @35
    @25
    @69
    @66
    @35
    @25
    w3a
    @51
    @48
    @13
    @6
    cW
    @10
    @34
    @19
    @29
    @31
    @32
    tltnle
    bicomd
    3com23
    3expa
    anbi2d
    rexbidva
    syl2anc
    mpbid
    archiabllem2
    pm2.61dan
end
