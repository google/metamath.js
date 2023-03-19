include "ccmp.mm"
include "cnlly.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "cnfldtop.mm"
include "wa.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "wss.mm"
include "crp.mm"
include "cc.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "cnfldtopn.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "c2.mm"
include "cdiv.mm"
include "ccl.mm"
include "a1i.mm"
include "cxr.mm"
include "cuni.mm"
include "elssuni.mm"
include "ad2antrr.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "syl6sseqr.mm"
include "simplr.mm"
include "sseldd.mm"
include "rphalfcl.mm"
include "ad2antrl.mm"
include "rpxrd.mm"
include "blopn.mm"
include "syl3anc.mm"
include "blcntr.mm"
include "opnneip.mm"
include "blssm.mm"
include "sscls.mm"
include "syl2anc.mm"
include "clt.mm"
include "wbr.mm"
include "rpxr.mm"
include "rphalflt.mm"
include "blsscls.mm"
include "syl23anc.mm"
include "simprr.mm"
include "sstrd.mm"
include "ssnei2.mm"
include "syl22anc.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "elind.mm"
include "ccld.mm"
include "cle.mm"
include "cr.mm"
include "clscld.mm"
include "caddc.mm"
include "abscld.mm"
include "rpred.mm"
include "readdcld.mm"
include "crab.mm"
include "eqid.mm"
include "blcls.mm"
include "wi.mm"
include "simpr.mm"
include "adantr.mm"
include "abs2difd.mm"
include "resubcld.mm"
include "subcld.mm"
include "letr.mm"
include "mpand.mm"
include "abssubd.mm"
include "wceq.mm"
include "cnmetdval.mm"
include "sylan.mm"
include "eqtr4d.mm"
include "breq1d.mm"
include "lesubadd2d.mm"
include "3imtr3d.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "ralrab.mm"
include "ssralv.mm"
include "sylc.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "wb.mm"
include "cnheibor.mm"
include "syl.mm"
include "mpbir2and.mm"
include "eleq1d.mm"
include "rexlimddv.mm"
include "rgen2.mm"
include "isnlly.mm"
include "mpbir2an.mm"

theorem cnllycmp
  let cJ: class J
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cnllycmp.1: |- J = ( TopOpen ` CCfld )


  assert |- J e. N-Locally Comp

  proof
    cJ
    ccmp
    cnlly
    wcel
    cJ
    ctop
    wcel
    #
    cJ
    vu
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vu
    vy
    cv
    #
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @7
    wral
    vx
    cJ
    wral
    cJ
    cnllycmp.1
    cnfldtop
    #
    @10
    vx
    vy
    cJ
    @7
    @7
    cJ
    wcel
    #
    @4
    @7
    wcel
    #
    wa
    #
    @4
    vr
    cv
    #
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    #
    co
    #
    @7
    wss
    #
    @10
    vr
    crp
    @16
    cc
    cxmt
    cfv
    wcel
    #
    @12
    @13
    @19
    vr
    crp
    wrex
    cnxmet
    vr
    @7
    @16
    @4
    cJ
    cc
    cJ
    cnllycmp.1
    cnfldtopn
    #
    mopni2
    mp3an1
    @14
    @15
    crp
    wcel
    #
    @19
    wa
    #
    wa
    #
    @4
    @15
    c2
    cdiv
    co
    #
    @17
    co
    #
    cJ
    ccl
    cfv
    cfv
    #
    @9
    wcel
    cJ
    @27
    crest
    co
    #
    ccmp
    wcel
    #
    @10
    @24
    @6
    @8
    @27
    @24
    @0
    @26
    @6
    wcel
    #
    @26
    @27
    wss
    #
    @27
    cc
    wss
    #
    @27
    @6
    wcel
    @0
    @24
    @11
    a1i
    #
    @24
    @0
    @26
    cJ
    wcel
    #
    @4
    @26
    wcel
    #
    @30
    @33
    @24
    @20
    @4
    cc
    wcel
    #
    @25
    cxr
    wcel
    #
    @34
    @20
    @24
    cnxmet
    a1i
    #
    @24
    @7
    cc
    @4
    @24
    @7
    cJ
    cuni
    #
    cc
    @12
    @7
    @39
    wss
    @13
    @23
    @7
    cJ
    elssuni
    ad2antrr
    cc
    cJ
    cJ
    cnllycmp.1
    cnfldtopon
    toponunii
    #
    syl6sseqr
    #
    @12
    @13
    @23
    simplr
    sseldd
    #
    @24
    @25
    @22
    @25
    crp
    wcel
    #
    @14
    @19
    @15
    rphalfcl
    ad2antrl
    #
    rpxrd
    #
    @16
    @4
    @25
    cJ
    cc
    @21
    blopn
    syl3anc
    @24
    @20
    @36
    @43
    @35
    @38
    @42
    @44
    @16
    @4
    @25
    cc
    blcntr
    syl3anc
    @4
    cJ
    @26
    opnneip
    syl3anc
    @24
    @0
    @26
    cc
    wss
    #
    @31
    @33
    @24
    @20
    @36
    @37
    @46
    @38
    @42
    @45
    @16
    @4
    @25
    cc
    blssm
    syl3anc
    #
    @26
    cJ
    cc
    @40
    sscls
    syl2anc
    @24
    @27
    @7
    cc
    @24
    @27
    @18
    @7
    @24
    @20
    @36
    @37
    @15
    cxr
    wcel
    #
    @25
    @15
    clt
    wbr
    #
    @27
    @18
    wss
    @38
    @42
    @45
    @22
    @48
    @14
    @19
    @15
    rpxr
    ad2antrl
    @22
    @49
    @14
    @19
    @15
    rphalflt
    ad2antrl
    @16
    @4
    @25
    @15
    cJ
    cc
    @21
    blsscls
    syl23anc
    @14
    @22
    @19
    simprr
    sstrd
    #
    @41
    sstrd
    #
    @5
    cJ
    @27
    @26
    cc
    @40
    ssnei2
    syl22anc
    @24
    @27
    @7
    wss
    @27
    @8
    wcel
    @50
    @27
    @7
    vx
    vex
    elpw2
    sylibr
    elind
    @24
    @29
    @27
    cJ
    ccld
    cfv
    wcel
    #
    vz
    cv
    #
    cabs
    cfv
    #
    vs
    cv
    #
    cle
    wbr
    #
    vz
    @27
    wral
    #
    vs
    cr
    wrex
    #
    @24
    @0
    @46
    @52
    @33
    @47
    @26
    cJ
    cc
    @40
    clscld
    syl2anc
    @24
    @4
    cabs
    cfv
    #
    @25
    caddc
    co
    #
    cr
    wcel
    @54
    @60
    cle
    wbr
    #
    vz
    @27
    wral
    #
    @58
    @24
    @59
    @25
    @24
    @4
    @42
    abscld
    #
    @24
    @25
    @44
    rpred
    #
    readdcld
    @24
    @27
    @4
    vw
    cv
    #
    @16
    co
    #
    @25
    cle
    wbr
    #
    vw
    cc
    crab
    #
    wss
    #
    @61
    vz
    @68
    wral
    #
    @62
    @24
    @20
    @36
    @37
    @69
    @38
    @42
    @45
    vw
    @16
    @4
    @25
    @68
    cJ
    cc
    @21
    @68
    eqid
    blcls
    syl3anc
    @24
    @4
    @53
    @16
    co
    #
    @25
    cle
    wbr
    #
    @61
    wi
    #
    vz
    cc
    wral
    @70
    @24
    @73
    vz
    cc
    @24
    @53
    cc
    wcel
    #
    wa
    #
    @53
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    @25
    cle
    wbr
    #
    @54
    @59
    cmin
    co
    #
    @25
    cle
    wbr
    #
    @72
    @61
    @75
    @79
    @77
    cle
    wbr
    #
    @78
    @80
    @75
    @53
    @4
    @24
    @74
    simpr
    #
    @24
    @36
    @74
    @42
    adantr
    #
    abs2difd
    @75
    @79
    cr
    wcel
    @77
    cr
    wcel
    @25
    cr
    wcel
    #
    @81
    @78
    wa
    @80
    wi
    @75
    @54
    @59
    @75
    @53
    @82
    abscld
    #
    @24
    @59
    cr
    wcel
    @74
    @63
    adantr
    #
    resubcld
    @75
    @76
    @75
    @53
    @4
    @82
    @83
    subcld
    abscld
    @24
    @84
    @74
    @64
    adantr
    #
    @79
    @77
    @25
    letr
    syl3anc
    mpand
    @75
    @77
    @71
    @25
    cle
    @75
    @77
    @4
    @53
    cmin
    co
    cabs
    cfv
    #
    @71
    @75
    @53
    @4
    @82
    @83
    abssubd
    @24
    @36
    @74
    @71
    @88
    wceq
    @42
    @4
    @53
    @16
    @16
    eqid
    cnmetdval
    sylan
    eqtr4d
    breq1d
    @75
    @54
    @59
    @25
    @85
    @86
    @87
    lesubadd2d
    3imtr3d
    ralrimiva
    @67
    @72
    @61
    vz
    vw
    cc
    @65
    @53
    wceq
    @66
    @71
    @25
    cle
    @65
    @53
    @4
    @16
    oveq2
    breq1d
    ralrab
    sylibr
    @61
    vz
    @27
    @68
    ssralv
    sylc
    @57
    @62
    vs
    @60
    cr
    @55
    @60
    wceq
    @56
    @61
    vz
    @27
    @55
    @60
    @54
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    @24
    @32
    @29
    @52
    @58
    wa
    wb
    @51
    vz
    @28
    cJ
    @27
    vs
    cnllycmp.1
    @28
    eqid
    cnheibor
    syl
    mpbir2and
    @3
    @29
    vu
    @27
    @9
    @1
    @27
    wceq
    @2
    @28
    ccmp
    @1
    @27
    cJ
    crest
    oveq2
    eleq1d
    rspcev
    syl2anc
    rexlimddv
    rgen2
    vx
    vy
    vu
    ccmp
    cJ
    isnlly
    mpbir2an
end
