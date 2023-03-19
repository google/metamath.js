include "cdir.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ctail.mm"
include "cfv.mm"
include "crn.mm"
include "cfbas.mm"
include "cpw.mm"
include "wss.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "wf.mm"
include "tailf.mm"
include "frn.mm"
include "syl.mm"
include "adantr.mm"
include "wex.mm"
include "n0.mm"
include "wfn.mm"
include "wi.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "ex.mm"
include "3syl.mm"
include "ne0i.mm"
include "syl6.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "wn.mm"
include "wceq.mm"
include "tailini.mm"
include "n0i.mm"
include "nrexdv.mm"
include "wb.mm"
include "fvelrnb.mm"
include "mtbird.mm"
include "df-nel.mm"
include "sylibr.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "wbr.mm"
include "dirge.mm"
include "3expb.mm"
include "sylan.mm"
include "ad2ant2r.mm"
include "cvv.mm"
include "vex.mm"
include "dirtr.mm"
include "exp32.mm"
include "mpan2.mm"
include "com23.mm"
include "ad2ant2rl.mm"
include "anim12d.mm"
include "expr.mm"
include "impr.mm"
include "eltail.mm"
include "mp3an3.mm"
include "adantrr.mm"
include "adantrl.mm"
include "3imtr4d.mm"
include "elin.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "sseq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimddv.mm"
include "ineq1.mm"
include "sseq2d.mm"
include "rexbidv.mm"
include "ineq2.mm"
include "sylan9bb.mm"
include "syl5ibcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "3jca.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "isfbas2.mm"
include "mpbir2and.mm"

theorem tailfb
  let cD: class D
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tailfb.1: |- X = dom D


  assert |- ( ( D e. DirRel /\ X =/= (/) ) -> ran ( tail ` D ) e. ( fBas ` X ) )

  proof
    cD
    cdir
    wcel
    #
    cX
    c0
    wne
    #
    wa
    #
    cD
    ctail
    cfv
    #
    crn
    #
    cX
    cfbas
    cfv
    wcel
    #
    @4
    cX
    cpw
    #
    wss
    #
    @4
    c0
    wne
    #
    c0
    @4
    wnel
    #
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wss
    #
    vz
    @4
    wrex
    #
    vy
    @4
    wral
    vx
    @4
    wral
    #
    w3a
    #
    @0
    @7
    @1
    @0
    cX
    @6
    @3
    wf
    #
    @7
    cD
    cX
    tailfb.1
    tailf
    #
    cX
    @6
    @3
    frn
    syl
    adantr
    @2
    @8
    @9
    @16
    @0
    @1
    @8
    @1
    @11
    cX
    wcel
    #
    vx
    wex
    @0
    @8
    vx
    cX
    n0
    @0
    @20
    @8
    vx
    @0
    @20
    @11
    @3
    cfv
    #
    @4
    wcel
    #
    @8
    @0
    @18
    @3
    cX
    wfn
    #
    @20
    @22
    wi
    @19
    cX
    @6
    @3
    ffn
    #
    @23
    @20
    @22
    cX
    @11
    @3
    fnfvelrn
    ex
    3syl
    @4
    @21
    ne0i
    syl6
    exlimdv
    syl5bi
    imp
    @2
    c0
    @4
    wcel
    #
    wn
    @9
    @2
    @25
    @21
    c0
    wceq
    #
    vx
    cX
    wrex
    #
    @0
    @27
    wn
    @1
    @0
    @26
    vx
    cX
    @0
    @20
    wa
    @11
    @21
    wcel
    @26
    wn
    @11
    cD
    cX
    tailfb.1
    tailini
    @21
    @11
    n0i
    syl
    nrexdv
    adantr
    @0
    @25
    @27
    wb
    #
    @1
    @0
    @18
    @23
    @28
    @19
    @24
    vx
    cX
    c0
    @3
    fvelrnb
    3syl
    adantr
    mtbird
    c0
    @4
    df-nel
    sylibr
    @2
    @15
    vx
    vy
    @4
    @4
    @0
    @11
    @4
    wcel
    #
    @12
    @4
    wcel
    #
    wa
    #
    @15
    wi
    @1
    @0
    @31
    vu
    cv
    #
    @3
    cfv
    #
    @11
    wceq
    #
    vu
    cX
    wrex
    #
    vv
    cv
    #
    @3
    cfv
    #
    @12
    wceq
    #
    vv
    cX
    wrex
    #
    wa
    #
    @15
    @0
    @18
    @23
    @31
    @40
    wb
    @19
    @24
    @23
    @29
    @35
    @30
    @39
    vu
    cX
    @11
    @3
    fvelrnb
    vv
    cX
    @12
    @3
    fvelrnb
    anbi12d
    3syl
    @40
    @34
    @38
    wa
    #
    vv
    cX
    wrex
    vu
    cX
    wrex
    @0
    @15
    @34
    @38
    vu
    vv
    cX
    cX
    reeanv
    @0
    @41
    @15
    vu
    vv
    cX
    cX
    @0
    @32
    cX
    wcel
    #
    @36
    cX
    wcel
    #
    wa
    #
    wa
    #
    @10
    @33
    @37
    cin
    #
    wss
    #
    vz
    @4
    wrex
    #
    @41
    @15
    @45
    @32
    vw
    cv
    #
    cD
    wbr
    #
    @36
    @49
    cD
    wbr
    #
    wa
    #
    @48
    vw
    cX
    @0
    @42
    @43
    @52
    vw
    cX
    wrex
    vw
    @32
    @36
    cD
    cX
    tailfb.1
    dirge
    3expb
    @45
    @49
    cX
    wcel
    #
    @52
    wa
    #
    wa
    #
    @49
    @3
    cfv
    #
    @4
    wcel
    #
    @56
    @46
    wss
    #
    @48
    @0
    @53
    @57
    @44
    @52
    @0
    @23
    @53
    @57
    @0
    @18
    @23
    @19
    @24
    syl
    cX
    @49
    @3
    fnfvelrn
    sylan
    ad2ant2r
    @55
    vx
    @56
    @46
    @55
    @11
    @56
    wcel
    #
    @11
    @33
    wcel
    #
    @11
    @37
    wcel
    #
    wa
    #
    @11
    @46
    wcel
    @55
    @49
    @11
    cD
    wbr
    #
    @32
    @11
    cD
    wbr
    #
    @36
    @11
    cD
    wbr
    #
    wa
    #
    @59
    @62
    @45
    @53
    @52
    @63
    @66
    wi
    @45
    @53
    wa
    @63
    @52
    @66
    @45
    @53
    @63
    @52
    @66
    wi
    @45
    @53
    @63
    wa
    wa
    @50
    @64
    @51
    @65
    @0
    @63
    @50
    @64
    wi
    #
    @44
    @53
    @0
    @63
    @67
    @0
    @50
    @63
    @64
    @0
    @11
    cvv
    wcel
    #
    @50
    @63
    @64
    wi
    wi
    vx
    vex
    #
    @0
    @68
    wa
    #
    @50
    @63
    @64
    @32
    @49
    @11
    cD
    cvv
    dirtr
    exp32
    mpan2
    com23
    imp
    ad2ant2rl
    @0
    @63
    @51
    @65
    wi
    #
    @44
    @53
    @0
    @63
    @71
    @0
    @51
    @63
    @65
    @0
    @68
    @51
    @63
    @65
    wi
    wi
    @69
    @70
    @51
    @63
    @65
    @36
    @49
    @11
    cD
    cvv
    dirtr
    exp32
    mpan2
    com23
    imp
    ad2ant2rl
    anim12d
    expr
    com23
    impr
    @0
    @53
    @59
    @63
    wb
    #
    @44
    @52
    @0
    @53
    @68
    @72
    @69
    @49
    @11
    cvv
    cD
    cX
    tailfb.1
    eltail
    mp3an3
    ad2ant2r
    @45
    @62
    @66
    wb
    @54
    @45
    @60
    @64
    @61
    @65
    @0
    @42
    @60
    @64
    wb
    #
    @43
    @0
    @42
    @68
    @73
    @69
    @32
    @11
    cvv
    cD
    cX
    tailfb.1
    eltail
    mp3an3
    adantrr
    @0
    @43
    @61
    @65
    wb
    #
    @42
    @0
    @43
    @68
    @74
    @69
    @36
    @11
    cvv
    cD
    cX
    tailfb.1
    eltail
    mp3an3
    adantrl
    anbi12d
    adantr
    3imtr4d
    @11
    @33
    @37
    elin
    syl6ibr
    ssrdv
    @47
    @58
    vz
    @56
    @4
    @10
    @56
    @46
    sseq1
    rspcev
    syl2anc
    rexlimddv
    @34
    @48
    @10
    @11
    @37
    cin
    #
    wss
    #
    vz
    @4
    wrex
    @38
    @15
    @34
    @47
    @76
    vz
    @4
    @34
    @46
    @75
    @10
    @33
    @11
    @37
    ineq1
    sseq2d
    rexbidv
    @38
    @76
    @14
    vz
    @4
    @38
    @75
    @13
    @10
    @37
    @12
    @11
    ineq2
    sseq2d
    rexbidv
    sylan9bb
    syl5ibcom
    rexlimdvva
    syl5bir
    sylbid
    adantr
    ralrimivv
    3jca
    @2
    cX
    cvv
    wcel
    #
    @5
    @7
    @17
    wa
    wb
    @0
    @77
    @1
    @0
    cX
    cD
    cdm
    cvv
    tailfb.1
    cD
    cdir
    dmexg
    syl5eqel
    adantr
    vx
    vy
    vz
    cvv
    cX
    @4
    isfbas2
    syl
    mpbir2and
end
