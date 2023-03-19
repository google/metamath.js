include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "cxp.mm"
include "brdomi.mm"
include "wa.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "crn.mm"
include "cfv.mm"
include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "wceq.mm"
include "wf.mm"
include "f1f.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "anim2d.mm"
include "adantld.mm"
include "elxp4.mm"
include "opelxp.mm"
include "3imtr4g.mm"
include "adantl.mm"
include "wb.mm"
include "wrex.mm"
include "elxp2.mm"
include "vex.mm"
include "fvex.mm"
include "opth.mm"
include "f1fveq.mm"
include "ancoms.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "ad2ant2l.mm"
include "imp.mm"
include "adantlr.mm"
include "sneq.mm"
include "dmeqd.mm"
include "unieqd.mm"
include "op1sta.mm"
include "syl6eq.mm"
include "rneqd.mm"
include "op2nda.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "eqeqan12d.mm"
include "ad2antlr.mm"
include "eqeq12.mm"
include "syl6bb.mm"
include "3bitr4d.mm"
include "exp53.mm"
include "com23.mm"
include "rexlimivv.mm"
include "rexlimdvv.mm"
include "syl2anb.mm"
include "com12.mm"
include "reldom.mm"
include "brrelexi.mm"
include "xpexg.mm"
include "sylancr.mm"
include "adantr.mm"
include "brrelex2i.mm"
include "dom3d.mm"
include "exlimddv.mm"

theorem xpdom2
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xpdom.2: |- C e. _V


  assert |- ( A ~<_ B -> ( C X. A ) ~<_ ( C X. B ) )

  proof
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    vf
    cv
    #
    wf1
    #
    cC
    cA
    cxp
    #
    cC
    cB
    cxp
    #
    cdom
    wbr
    vf
    cA
    cB
    vf
    brdomi
    @0
    @2
    wa
    vx
    vy
    @3
    @4
    vx
    cv
    #
    csn
    #
    cdm
    #
    cuni
    #
    @6
    crn
    #
    cuni
    #
    @1
    cfv
    #
    cop
    #
    vy
    cv
    #
    csn
    #
    cdm
    #
    cuni
    #
    @14
    crn
    #
    cuni
    #
    @1
    cfv
    #
    cop
    #
    cvv
    cvv
    @2
    @5
    @3
    wcel
    #
    @12
    @4
    wcel
    #
    wi
    @0
    @2
    @5
    @8
    @10
    cop
    wceq
    #
    @8
    cC
    wcel
    #
    @10
    cA
    wcel
    #
    wa
    #
    wa
    @24
    @11
    cB
    wcel
    #
    wa
    #
    @21
    @22
    @2
    @26
    @28
    @23
    @2
    @25
    @27
    @24
    @2
    cA
    cB
    @1
    wf
    #
    @25
    @27
    wi
    cA
    cB
    @1
    f1f
    @29
    @25
    @27
    cA
    cB
    @10
    @1
    ffvelrn
    ex
    syl
    anim2d
    adantld
    @5
    cC
    cA
    elxp4
    @8
    @11
    cC
    cB
    opelxp
    3imtr4g
    adantl
    @2
    @21
    @13
    @3
    wcel
    #
    wa
    #
    @12
    @20
    wceq
    #
    @5
    @13
    wceq
    #
    wb
    #
    wi
    @0
    @31
    @2
    @34
    @21
    @5
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
    vw
    cA
    wrex
    vz
    cC
    wrex
    #
    @13
    vv
    cv
    #
    vu
    cv
    #
    cop
    #
    wceq
    #
    vu
    cA
    wrex
    vv
    cC
    wrex
    #
    @2
    @34
    wi
    #
    @30
    vz
    vw
    @5
    cC
    cA
    elxp2
    vv
    vu
    @13
    cC
    cA
    elxp2
    @39
    @44
    @45
    @39
    @43
    @45
    vv
    vu
    cC
    cA
    @38
    @40
    cC
    wcel
    #
    @41
    cA
    wcel
    #
    wa
    #
    @43
    @45
    wi
    #
    wi
    vz
    vw
    cC
    cA
    @35
    cC
    wcel
    #
    @36
    cA
    wcel
    #
    wa
    #
    @48
    @38
    @49
    @52
    @48
    @38
    @43
    @2
    @34
    @52
    @48
    wa
    #
    @38
    @43
    wa
    #
    wa
    @2
    wa
    @35
    @36
    @1
    cfv
    #
    cop
    #
    @40
    @41
    @1
    cfv
    #
    cop
    #
    wceq
    #
    @35
    @40
    wceq
    #
    @36
    @41
    wceq
    #
    wa
    #
    @32
    @33
    @53
    @2
    @59
    @62
    wb
    #
    @54
    @53
    @2
    @63
    @51
    @47
    @2
    @63
    wi
    @50
    @46
    @51
    @47
    wa
    #
    @2
    @63
    @59
    @60
    @55
    @57
    wceq
    #
    wa
    @64
    @2
    wa
    #
    @62
    @35
    @55
    @40
    @57
    vz
    vex
    #
    @36
    @1
    fvex
    opth
    @66
    @65
    @61
    @60
    @2
    @64
    @65
    @61
    wb
    cA
    cB
    @36
    @41
    @1
    f1fveq
    ancoms
    anbi2d
    syl5bb
    ex
    ad2ant2l
    imp
    adantlr
    @54
    @32
    @59
    wb
    @53
    @2
    @38
    @43
    @12
    @56
    @20
    @58
    @38
    @8
    @35
    @11
    @55
    @38
    @8
    @37
    csn
    #
    cdm
    #
    cuni
    @35
    @38
    @7
    @69
    @38
    @6
    @68
    @5
    @37
    sneq
    #
    dmeqd
    unieqd
    @35
    @36
    @67
    vw
    vex
    #
    op1sta
    syl6eq
    @38
    @10
    @36
    @1
    @38
    @10
    @68
    crn
    #
    cuni
    @36
    @38
    @9
    @72
    @38
    @6
    @68
    @70
    rneqd
    unieqd
    @35
    @36
    @67
    @71
    op2nda
    syl6eq
    fveq2d
    opeq12d
    @43
    @16
    @40
    @19
    @57
    @43
    @16
    @42
    csn
    #
    cdm
    #
    cuni
    @40
    @43
    @15
    @74
    @43
    @14
    @73
    @13
    @42
    sneq
    #
    dmeqd
    unieqd
    @40
    @41
    vv
    vex
    #
    vu
    vex
    #
    op1sta
    syl6eq
    @43
    @18
    @41
    @1
    @43
    @18
    @73
    crn
    #
    cuni
    @41
    @43
    @17
    @78
    @43
    @14
    @73
    @75
    rneqd
    unieqd
    @40
    @41
    @76
    @77
    op2nda
    syl6eq
    fveq2d
    opeq12d
    eqeqan12d
    ad2antlr
    @54
    @33
    @62
    wb
    @53
    @2
    @54
    @33
    @37
    @42
    wceq
    @62
    @5
    @37
    @13
    @42
    eqeq12
    @35
    @36
    @40
    @41
    @67
    @71
    opth
    syl6bb
    ad2antlr
    3bitr4d
    exp53
    com23
    rexlimivv
    rexlimdvv
    imp
    syl2anb
    com12
    adantl
    @0
    @3
    cvv
    wcel
    #
    @2
    @0
    cC
    cvv
    wcel
    #
    cA
    cvv
    wcel
    @79
    xpdom.2
    cA
    cB
    cdom
    reldom
    brrelexi
    cC
    cA
    cvv
    cvv
    xpexg
    sylancr
    adantr
    @0
    @4
    cvv
    wcel
    #
    @2
    @0
    @80
    cB
    cvv
    wcel
    @81
    xpdom.2
    cA
    cB
    cdom
    reldom
    brrelex2i
    cC
    cB
    cvv
    cvv
    xpexg
    sylancr
    adantr
    dom3d
    exlimddv
end
