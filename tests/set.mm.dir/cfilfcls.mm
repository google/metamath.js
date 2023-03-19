include "ccfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfcls.mm"
include "co.mm"
include "cflim.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "cuni.mm"
include "eqid.mm"
include "fclselbas.mm"
include "adantl.mm"
include "ctopon.mm"
include "wceq.mm"
include "cxmt.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cima.mm"
include "cc0.mm"
include "cico.mm"
include "wss.mm"
include "wrex.mm"
include "crp.mm"
include "cfil.mm"
include "crab.mm"
include "df-cfil.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "xmetunirn.mm"
include "sylib.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "adantr.mm"
include "mopntopon.mm"
include "syl.mm"
include "toponuni.mm"
include "eleqtrrd.mm"
include "cbl.mm"
include "mopni2.mm"
include "3expb.mm"
include "sylan.mm"
include "cfilfil.mm"
include "mpancom.mm"
include "ad2antrr.mm"
include "c2.mm"
include "cdiv.mm"
include "simpll.mm"
include "rphalfcl.mm"
include "cfil3i.mm"
include "syl3anc.mm"
include "simprr.mm"
include "cxr.mm"
include "rpxr.mm"
include "ad2antlr.mm"
include "blssm.mm"
include "cin.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "simpllr.mm"
include "blopn.mm"
include "blcntr.mm"
include "fclsopni.mm"
include "syl13anc.mm"
include "n0.mm"
include "elin.mm"
include "cr.mm"
include "simplrl.mm"
include "rpred.mm"
include "blhalf.mm"
include "syl22anc.mm"
include "sselda.mm"
include "adantrr.mm"
include "simprl.mm"
include "wb.mm"
include "blcom.mm"
include "mpbid.mm"
include "sstrd.mm"
include "ex.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "mpd.mm"
include "filss.mm"
include "rexlimddv.mm"
include "ad2ant2r.mm"
include "toponss.mm"
include "expr.mm"
include "ralrimiva.mm"
include "flimopn.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ssrdv.mm"
include "flimfcls.mm"
include "a1i.mm"
include "eqssd.mm"

theorem cfilfcls
  let cD: class D
  let cF: class F
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let vr: setvar r
  let cG: class G
  let cR: class R
  let cY: class Y
  let vd: setvar d
  assume cfilfcls.1: |- J = ( MetOpen ` D )
  assume cfilfcls.2: |- X = dom dom D


  assert |- ( F e. ( CauFil ` D ) -> ( J fClus F ) = ( J fLim F ) )

  proof
    cF
    cD
    ccfil
    cfv
    wcel
    #
    cJ
    cF
    cfcls
    co
    #
    cJ
    cF
    cflim
    co
    #
    @0
    vx
    @1
    @2
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    #
    @5
    @3
    cX
    wcel
    #
    @3
    vy
    cv
    #
    wcel
    #
    @8
    cF
    wcel
    #
    wi
    #
    vy
    cJ
    wral
    #
    @6
    @3
    cJ
    cuni
    #
    cX
    @4
    @3
    @13
    wcel
    @0
    @3
    cF
    cJ
    @13
    @13
    eqid
    fclselbas
    adantl
    @6
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cX
    @13
    wceq
    @6
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    @14
    @0
    @16
    @4
    @0
    cD
    cD
    cdm
    cdm
    #
    cxmt
    cfv
    #
    @15
    @0
    cD
    cxmt
    crn
    cuni
    #
    wcel
    cD
    @18
    wcel
    @0
    ccfil
    cdm
    @19
    cD
    vd
    @19
    vd
    cv
    #
    @8
    @8
    cxp
    cima
    cc0
    @3
    cico
    co
    wss
    vy
    vf
    cv
    wrex
    vx
    crp
    wral
    vf
    @20
    cdm
    cdm
    cfil
    cfv
    crab
    ccfil
    vx
    vy
    vf
    vd
    df-cfil
    dmmptss
    cF
    cD
    ccfil
    elfvdm
    sseldi
    cD
    xmetunirn
    sylib
    cX
    @17
    cxmt
    cfilfcls.2
    fveq2i
    syl6eleqr
    #
    adantr
    #
    cD
    cJ
    cX
    cfilfcls.1
    mopntopon
    syl
    #
    cX
    cJ
    toponuni
    syl
    eleqtrrd
    #
    @6
    @11
    vy
    cJ
    @6
    @8
    cJ
    wcel
    #
    @9
    @10
    @6
    @25
    @9
    wa
    #
    wa
    #
    @3
    vr
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @8
    wss
    #
    @10
    vr
    crp
    @6
    @16
    @26
    @31
    vr
    crp
    wrex
    #
    @22
    @16
    @25
    @9
    @32
    vr
    @8
    cD
    @3
    cJ
    cX
    cfilfcls.1
    mopni2
    3expb
    sylan
    @27
    @28
    crp
    wcel
    #
    @31
    wa
    #
    wa
    cF
    cX
    cfil
    cfv
    wcel
    #
    @30
    cF
    wcel
    #
    @8
    cX
    wss
    #
    @31
    @10
    @6
    @35
    @26
    @34
    @0
    @35
    @4
    @16
    @0
    @35
    @21
    cD
    cF
    cX
    cfilfil
    mpancom
    adantr
    #
    ad2antrr
    @6
    @33
    @36
    @26
    @31
    @6
    @33
    wa
    #
    @8
    @28
    c2
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    @29
    co
    #
    cF
    wcel
    #
    @36
    vy
    cX
    @39
    @16
    @0
    @41
    crp
    wcel
    #
    @43
    vy
    cX
    wrex
    @6
    @16
    @33
    @22
    adantr
    #
    @0
    @4
    @33
    simpll
    @39
    @40
    crp
    wcel
    #
    @44
    @33
    @46
    @6
    @28
    rphalfcl
    adantl
    #
    @40
    rphalfcl
    syl
    vy
    cD
    @41
    cF
    cX
    cfil3i
    syl3anc
    @39
    @8
    cX
    wcel
    #
    @43
    wa
    #
    wa
    #
    @35
    @43
    @30
    cX
    wss
    #
    @42
    @30
    wss
    #
    @36
    @6
    @35
    @33
    @49
    @38
    ad2antrr
    @39
    @48
    @43
    simprr
    #
    @50
    @16
    @7
    @28
    cxr
    wcel
    #
    @51
    @39
    @16
    @49
    @45
    adantr
    #
    @6
    @7
    @33
    @49
    @24
    ad2antrr
    #
    @33
    @54
    @6
    @49
    @28
    rpxr
    ad2antlr
    cD
    @3
    @28
    cX
    blssm
    syl3anc
    @50
    vz
    cv
    #
    @3
    @40
    @29
    co
    #
    @42
    cin
    #
    wcel
    #
    vz
    wex
    #
    @52
    @50
    @59
    c0
    wne
    #
    @61
    @50
    @4
    @58
    cJ
    wcel
    #
    @3
    @58
    wcel
    #
    @43
    @62
    @0
    @4
    @33
    @49
    simpllr
    @50
    @16
    @7
    @40
    cxr
    wcel
    #
    @63
    @55
    @56
    @50
    @46
    @65
    @39
    @46
    @49
    @47
    adantr
    #
    @40
    rpxr
    #
    syl
    #
    cD
    @3
    @40
    cJ
    cX
    cfilfcls.1
    blopn
    syl3anc
    @50
    @16
    @7
    @46
    @64
    @55
    @56
    @66
    cD
    @3
    @40
    cX
    blcntr
    syl3anc
    @53
    @3
    @42
    @58
    cF
    cJ
    fclsopni
    syl13anc
    vz
    @59
    n0
    sylib
    @50
    @60
    @52
    vz
    @60
    @57
    @58
    wcel
    #
    @57
    @42
    wcel
    #
    wa
    #
    @50
    @52
    @57
    @58
    @42
    elin
    @50
    @71
    @52
    @50
    @71
    wa
    #
    @42
    @57
    @40
    @29
    co
    #
    @30
    @72
    @16
    @48
    @40
    cr
    wcel
    @70
    @42
    @73
    wss
    @50
    @16
    @71
    @55
    adantr
    #
    @39
    @48
    @43
    @71
    simplrl
    @72
    @40
    @50
    @46
    @71
    @66
    adantr
    #
    rpred
    @50
    @69
    @70
    simprr
    @40
    cD
    cX
    @8
    @57
    blhalf
    syl22anc
    @72
    @16
    @57
    cX
    wcel
    #
    @28
    cr
    wcel
    @3
    @73
    wcel
    #
    @73
    @30
    wss
    @74
    @50
    @69
    @76
    @70
    @50
    @58
    cX
    @57
    @50
    @16
    @7
    @65
    @58
    cX
    wss
    @55
    @56
    @68
    cD
    @3
    @40
    cX
    blssm
    syl3anc
    sselda
    adantrr
    #
    @72
    @28
    @6
    @33
    @49
    @71
    simpllr
    rpred
    @72
    @69
    @77
    @50
    @69
    @70
    simprl
    @72
    @16
    @65
    @7
    @76
    @69
    @77
    wb
    @74
    @72
    @46
    @65
    @75
    @67
    syl
    @50
    @7
    @71
    @56
    adantr
    @78
    @57
    cD
    @3
    @40
    cX
    blcom
    syl22anc
    mpbid
    @28
    cD
    cX
    @57
    @3
    blhalf
    syl22anc
    sstrd
    ex
    syl5bi
    exlimdv
    mpd
    @42
    @30
    cF
    cX
    filss
    syl13anc
    rexlimddv
    ad2ant2r
    @27
    @37
    @34
    @6
    @14
    @26
    @37
    @23
    @14
    @25
    @37
    @9
    @8
    cJ
    cX
    toponss
    adantrr
    sylan
    adantr
    @27
    @33
    @31
    simprr
    @30
    @8
    cF
    cX
    filss
    syl13anc
    rexlimddv
    expr
    ralrimiva
    @6
    @14
    @35
    @5
    @7
    @12
    wa
    wb
    @23
    @38
    vy
    @3
    cF
    cJ
    cX
    flimopn
    syl2anc
    mpbir2and
    ex
    ssrdv
    @2
    @1
    wss
    @0
    cF
    cJ
    flimfcls
    a1i
    eqssd
end
