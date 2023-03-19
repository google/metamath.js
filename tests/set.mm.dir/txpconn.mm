include "cpconn.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "ctop.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cii.mm"
include "ccn.mm"
include "wrex.mm"
include "cuni.mm"
include "wral.mm"
include "pconntop.mm"
include "txtop.mm"
include "syl2an.mm"
include "cxp.mm"
include "cop.mm"
include "w3a.mm"
include "an6.mm"
include "eqid.mm"
include "pconncn.mm"
include "anim12i.mm"
include "sylbir.mm"
include "reeanv.mm"
include "sylibr.mm"
include "cicc.mm"
include "cmpt.mm"
include "iiuni.mm"
include "txcnmpt.mm"
include "ad2antrl.mm"
include "0elunit.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "simprrl.mm"
include "simpld.mm"
include "simprrr.mm"
include "syl5eq.mm"
include "1elunit.mm"
include "simprd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "3expa.mm"
include "ralrimivva.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralxp.mm"
include "anbi1d.mm"
include "2ralbidv.mm"
include "syl5bb.mm"
include "txuni.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "mpbid.mm"
include "ispconn.mm"
include "sylanbrc.mm"

theorem txpconn
  let cR: class R
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vi: setvar i
  let cA: class A
  let cF: class F
  let cV: class V


  assert |- ( ( R e. PConn /\ S e. PConn ) -> ( R tX S ) e. PConn )

  proof
    cR
    cpconn
    wcel
    #
    cS
    cpconn
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    ctop
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    #
    vu
    cv
    #
    wceq
    #
    c1
    @5
    cfv
    #
    vv
    cv
    #
    wceq
    #
    wa
    #
    vf
    cii
    @3
    ccn
    co
    #
    wrex
    #
    vv
    @3
    cuni
    #
    wral
    #
    vu
    @15
    wral
    #
    @3
    cpconn
    wcel
    @0
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @4
    @1
    cR
    pconntop
    #
    cS
    pconntop
    #
    cR
    cS
    txtop
    syl2an
    @2
    @14
    vv
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    wral
    #
    vu
    @24
    wral
    #
    @17
    @2
    @6
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @9
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    wa
    #
    vf
    @13
    wrex
    #
    vw
    @23
    wral
    vz
    @22
    wral
    #
    vy
    @23
    wral
    vx
    @22
    wral
    @26
    @2
    @37
    vx
    vy
    @22
    @23
    @2
    @27
    @22
    wcel
    #
    @28
    @23
    wcel
    #
    wa
    #
    wa
    @36
    vz
    vw
    @22
    @23
    @2
    @40
    @31
    @22
    wcel
    #
    @32
    @23
    wcel
    #
    wa
    #
    @36
    @2
    @40
    @43
    w3a
    #
    cc0
    vg
    cv
    #
    cfv
    #
    @27
    wceq
    #
    c1
    @45
    cfv
    #
    @31
    wceq
    #
    wa
    #
    cc0
    vh
    cv
    #
    cfv
    #
    @28
    wceq
    #
    c1
    @51
    cfv
    #
    @32
    wceq
    #
    wa
    #
    wa
    #
    vh
    cii
    cS
    ccn
    co
    #
    wrex
    vg
    cii
    cR
    ccn
    co
    #
    wrex
    #
    @36
    @44
    @50
    vg
    @59
    wrex
    #
    @56
    vh
    @58
    wrex
    #
    wa
    #
    @60
    @44
    @0
    @38
    @41
    w3a
    #
    @1
    @39
    @42
    w3a
    #
    wa
    @63
    @0
    @38
    @41
    @1
    @39
    @42
    an6
    @64
    @61
    @65
    @62
    @27
    @31
    vg
    cR
    @22
    @22
    eqid
    #
    pconncn
    @28
    @32
    vh
    cS
    @23
    @23
    eqid
    #
    pconncn
    anim12i
    sylbir
    @50
    @56
    vg
    vh
    @59
    @58
    reeanv
    sylibr
    @44
    @57
    @36
    vg
    vh
    @59
    @58
    @44
    @45
    @59
    wcel
    @51
    @58
    wcel
    wa
    #
    @57
    @36
    @44
    @68
    @57
    wa
    wa
    #
    vt
    cc0
    c1
    cicc
    co
    #
    vt
    cv
    #
    @45
    cfv
    #
    @71
    @51
    cfv
    #
    cop
    #
    cmpt
    #
    @13
    wcel
    #
    cc0
    @75
    cfv
    #
    @29
    wceq
    #
    c1
    @75
    cfv
    #
    @33
    wceq
    #
    @36
    @68
    @76
    @44
    @57
    vt
    cR
    cS
    cii
    @45
    @51
    @75
    @70
    iiuni
    @75
    eqid
    #
    txcnmpt
    ad2antrl
    @69
    @77
    @46
    @52
    cop
    #
    @29
    cc0
    @70
    wcel
    @77
    @82
    wceq
    0elunit
    vt
    cc0
    @74
    @82
    @70
    @75
    @71
    cc0
    wceq
    @72
    @46
    @73
    @52
    @71
    cc0
    @45
    fveq2
    @71
    cc0
    @51
    fveq2
    opeq12d
    @81
    @46
    @52
    opex
    fvmpt
    ax-mp
    @69
    @46
    @27
    @52
    @28
    @69
    @47
    @49
    @44
    @68
    @50
    @56
    simprrl
    #
    simpld
    @69
    @53
    @55
    @44
    @68
    @50
    @56
    simprrr
    #
    simpld
    opeq12d
    syl5eq
    @69
    @79
    @48
    @54
    cop
    #
    @33
    c1
    @70
    wcel
    @79
    @85
    wceq
    1elunit
    vt
    c1
    @74
    @85
    @70
    @75
    @71
    c1
    wceq
    @72
    @48
    @73
    @54
    @71
    c1
    @45
    fveq2
    @71
    c1
    @51
    fveq2
    opeq12d
    @81
    @48
    @54
    opex
    fvmpt
    ax-mp
    @69
    @48
    @31
    @54
    @32
    @69
    @47
    @49
    @83
    simprd
    @69
    @53
    @55
    @84
    simprd
    opeq12d
    syl5eq
    @35
    @78
    @80
    wa
    vf
    @75
    @13
    @5
    @75
    wceq
    #
    @30
    @78
    @34
    @80
    @86
    @6
    @77
    @29
    cc0
    @5
    @75
    fveq1
    eqeq1d
    @86
    @9
    @79
    @33
    c1
    @5
    @75
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    expr
    rexlimdvva
    mpd
    3expa
    ralrimivva
    ralrimivva
    @25
    @37
    vu
    vx
    vy
    @22
    @23
    @25
    @8
    @34
    wa
    #
    vf
    @13
    wrex
    #
    vw
    @23
    wral
    vz
    @22
    wral
    @7
    @29
    wceq
    #
    @37
    @14
    @88
    vv
    vz
    vw
    @22
    @23
    @10
    @33
    wceq
    #
    @12
    @87
    vf
    @13
    @90
    @11
    @34
    @8
    @10
    @33
    @9
    eqeq2
    anbi2d
    rexbidv
    ralxp
    @89
    @88
    @36
    vz
    vw
    @22
    @23
    @89
    @87
    @35
    vf
    @13
    @89
    @8
    @30
    @34
    @7
    @29
    @6
    eqeq2
    anbi1d
    rexbidv
    2ralbidv
    syl5bb
    ralxp
    sylibr
    @2
    @25
    @16
    vu
    @24
    @15
    @0
    @18
    @19
    @24
    @15
    wceq
    @1
    @20
    @21
    cR
    cS
    @22
    @23
    @66
    @67
    txuni
    syl2an
    #
    @2
    @14
    vv
    @24
    @15
    @91
    raleqdv
    raleqbidv
    mpbid
    vu
    vv
    vf
    @3
    @15
    @15
    eqid
    ispconn
    sylanbrc
end
