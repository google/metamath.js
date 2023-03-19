include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "c0r.mm"
include "cltr.mm"
include "wbr.mm"
include "cmr.mm"
include "co.mm"
include "ltrelsr.mm"
include "brel.mm"
include "simprd.mm"
include "anim12i.mm"
include "cv.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "wi.mm"
include "cnp.mm"
include "df-nr.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "cltp.mm"
include "gt0srpr.mm"
include "anbi12i.mm"
include "cmp.mm"
include "cpp.mm"
include "simprr.mm"
include "mulclpr.mm"
include "addclpr.mm"
include "syl2an.mm"
include "an4s.mm"
include "wrex.mm"
include "ltexpri.mm"
include "oveq12.mm"
include "oveq1d.mm"
include "distrpr.mm"
include "syl5eqr.mm"
include "vex.mm"
include "mulcompr.mm"
include "caovdir.mm"
include "oveq12i.mm"
include "ovex.mm"
include "addcompr.mm"
include "addasspr.mm"
include "caov4.mm"
include "3eqtr4i.mm"
include "caov12.mm"
include "3eqtr4g.mm"
include "oveqan12rd.mm"
include "eqtr3d.mm"
include "eqtr3i.mm"
include "caov32.mm"
include "oveq2i.mm"
include "3eqtr3g.mm"
include "addcanpr.mm"
include "syl5.mm"
include "eqcom.mm"
include "ltaddpr2.mm"
include "syl5bi.mm"
include "adantl.mm"
include "syld.mm"
include "sylan.mm"
include "a1d.mm"
include "exp4a.mm"
include "com34.mm"
include "rexlimdv.mm"
include "expl.mm"
include "com24.mm"
include "rexlimiv.mm"
include "syl2im.mm"
include "imp.mm"
include "com12.mm"
include "syl2anc.mm"
include "mulsrpr.mm"
include "syl6bb.mm"
include "sylibrd.mm"
include "2ecoptocl.mm"
include "mpcom.mm"

theorem mulgt0sr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h


  assert |- ( ( 0R <R A /\ 0R <R B ) -> 0R <R ( A .R B ) )

  proof
    cA
    cnr
    wcel
    #
    cB
    cnr
    wcel
    #
    wa
    c0r
    cA
    cltr
    wbr
    #
    c0r
    cB
    cltr
    wbr
    #
    wa
    #
    c0r
    cA
    cB
    cmr
    co
    #
    cltr
    wbr
    #
    @2
    @0
    @3
    @1
    @2
    c0r
    cnr
    wcel
    #
    @0
    c0r
    cA
    cnr
    cnr
    cltr
    ltrelsr
    brel
    simprd
    @3
    @7
    @1
    c0r
    cB
    cnr
    cnr
    cltr
    ltrelsr
    brel
    simprd
    anim12i
    c0r
    vx
    cv
    #
    vy
    cv
    #
    cop
    cer
    cec
    #
    cltr
    wbr
    #
    c0r
    vz
    cv
    #
    vw
    cv
    #
    cop
    cer
    cec
    #
    cltr
    wbr
    #
    wa
    #
    c0r
    @10
    @14
    cmr
    co
    #
    cltr
    wbr
    #
    wi
    @2
    @15
    wa
    #
    c0r
    cA
    @14
    cmr
    co
    #
    cltr
    wbr
    #
    wi
    @4
    @6
    wi
    vx
    vy
    vz
    vw
    cA
    cB
    cnp
    cnp
    cer
    cnr
    df-nr
    @10
    cA
    wceq
    #
    @16
    @19
    @18
    @21
    @22
    @11
    @2
    @15
    @10
    cA
    c0r
    cltr
    breq2
    anbi1d
    @22
    @17
    @20
    c0r
    cltr
    @10
    cA
    @14
    cmr
    oveq1
    breq2d
    imbi12d
    @14
    cB
    wceq
    #
    @19
    @4
    @21
    @6
    @23
    @15
    @3
    @2
    @14
    cB
    c0r
    cltr
    breq2
    anbi2d
    @23
    @20
    @5
    c0r
    cltr
    @14
    cB
    cA
    cmr
    oveq2
    breq2d
    imbi12d
    @16
    @9
    @8
    cltp
    wbr
    #
    @13
    @12
    cltp
    wbr
    #
    wa
    #
    @8
    cnp
    wcel
    #
    @9
    cnp
    wcel
    #
    wa
    #
    @12
    cnp
    wcel
    #
    @13
    cnp
    wcel
    #
    wa
    wa
    #
    @18
    @11
    @24
    @15
    @25
    @8
    @9
    gt0srpr
    @12
    @13
    gt0srpr
    anbi12i
    @32
    @26
    @8
    @13
    cmp
    co
    #
    @9
    @12
    cmp
    co
    #
    cpp
    co
    #
    @8
    @12
    cmp
    co
    #
    @9
    @13
    cmp
    co
    #
    cpp
    co
    #
    cltp
    wbr
    #
    @18
    @32
    @31
    @38
    cnp
    wcel
    #
    @26
    @39
    wi
    @29
    @30
    @31
    simprr
    @27
    @30
    @28
    @31
    @40
    @27
    @30
    wa
    @36
    cnp
    wcel
    @37
    cnp
    wcel
    @40
    @28
    @31
    wa
    @8
    @12
    mulclpr
    @9
    @13
    mulclpr
    @36
    @37
    addclpr
    syl2an
    an4s
    @26
    @31
    @40
    wa
    #
    @39
    @24
    @25
    @41
    @39
    wi
    #
    @24
    @9
    vv
    cv
    #
    cpp
    co
    #
    @8
    wceq
    #
    vv
    cnp
    wrex
    @25
    @13
    vu
    cv
    #
    cpp
    co
    #
    @12
    wceq
    #
    vu
    cnp
    wrex
    #
    @42
    vv
    @9
    @8
    ltexpri
    vu
    @13
    @12
    ltexpri
    @45
    @49
    @42
    wi
    vv
    cnp
    @43
    cnp
    wcel
    #
    @41
    @49
    @45
    @39
    @50
    @31
    @40
    @49
    @45
    @39
    wi
    #
    wi
    @50
    @31
    wa
    #
    @40
    wa
    #
    @48
    @51
    vu
    cnp
    @53
    @46
    cnp
    wcel
    #
    @45
    @48
    @39
    @53
    @54
    @45
    @48
    @39
    @53
    @45
    @48
    wa
    #
    @39
    wi
    #
    @54
    @52
    @43
    @13
    cmp
    co
    #
    cnp
    wcel
    #
    @40
    @56
    @43
    @13
    mulclpr
    @58
    @40
    wa
    #
    @55
    @38
    @35
    @43
    @46
    cmp
    co
    #
    cpp
    co
    #
    wceq
    #
    @39
    @55
    @57
    @38
    cpp
    co
    #
    @57
    @61
    cpp
    co
    #
    wceq
    @59
    @62
    @55
    @36
    @37
    @57
    cpp
    co
    #
    cpp
    co
    #
    @57
    @34
    @60
    cpp
    co
    #
    cpp
    co
    #
    @33
    cpp
    co
    #
    @63
    @64
    @55
    @44
    @47
    cmp
    co
    #
    @65
    cpp
    co
    @66
    @69
    @55
    @70
    @36
    @65
    cpp
    @44
    @8
    @47
    @12
    cmp
    oveq12
    oveq1d
    @48
    @45
    @70
    @68
    @65
    @33
    cpp
    @48
    @37
    @9
    @46
    cmp
    co
    #
    cpp
    co
    #
    @57
    @60
    cpp
    co
    #
    cpp
    co
    #
    @34
    @73
    cpp
    co
    @70
    @68
    @48
    @72
    @34
    @73
    cpp
    @48
    @72
    @9
    @47
    cmp
    co
    @34
    @9
    @13
    @46
    distrpr
    @47
    @12
    @9
    cmp
    oveq2
    syl5eqr
    oveq1d
    @44
    @13
    cmp
    co
    #
    @44
    @46
    cmp
    co
    #
    cpp
    co
    @65
    @71
    @60
    cpp
    co
    #
    cpp
    co
    @70
    @74
    @75
    @65
    @76
    @77
    cpp
    vf
    vg
    vh
    @9
    @43
    @13
    cpp
    cmp
    vy
    vex
    #
    vv
    vex
    #
    vw
    vex
    vf
    cv
    #
    vg
    cv
    #
    mulcompr
    #
    @80
    @81
    vh
    cv
    #
    distrpr
    #
    caovdir
    #
    vf
    vg
    vh
    @9
    @43
    @46
    cpp
    cmp
    @78
    @79
    vu
    vex
    @82
    @84
    caovdir
    oveq12i
    @44
    @13
    @46
    distrpr
    vf
    vg
    vh
    @37
    @71
    @57
    @60
    cpp
    @9
    @13
    cmp
    ovex
    @9
    @46
    cmp
    ovex
    @43
    @13
    cmp
    ovex
    #
    @80
    @81
    addcompr
    #
    @80
    @81
    @83
    addasspr
    #
    @43
    @46
    cmp
    ovex
    #
    caov4
    3eqtr4i
    vf
    vg
    vh
    @57
    @34
    @60
    cpp
    @86
    @9
    @12
    cmp
    ovex
    @89
    @87
    @88
    caov12
    3eqtr4g
    @45
    @65
    @75
    @33
    @85
    @44
    @8
    @13
    cmp
    oveq1
    syl5eqr
    oveqan12rd
    eqtr3d
    @38
    @57
    cpp
    co
    @66
    @63
    @36
    @37
    @57
    addasspr
    @38
    @57
    addcompr
    eqtr3i
    @57
    @33
    cpp
    co
    @67
    cpp
    co
    @57
    @33
    @67
    cpp
    co
    #
    cpp
    co
    @69
    @64
    @57
    @33
    @67
    addasspr
    vf
    vg
    vh
    @57
    @67
    @33
    cpp
    @86
    @34
    @60
    cpp
    ovex
    @8
    @13
    cmp
    ovex
    @87
    @88
    caov32
    @61
    @90
    @57
    cpp
    @33
    @34
    @60
    addasspr
    oveq2i
    3eqtr4i
    3eqtr3g
    @57
    @38
    @61
    addcanpr
    syl5
    @40
    @62
    @39
    wi
    @58
    @62
    @61
    @38
    wceq
    @40
    @39
    @38
    @61
    eqcom
    @35
    @60
    @38
    ltaddpr2
    syl5bi
    adantl
    syld
    sylan
    a1d
    exp4a
    com34
    rexlimdv
    expl
    com24
    rexlimiv
    syl2im
    imp
    com12
    syl2anc
    @32
    @18
    c0r
    @38
    @35
    cop
    cer
    cec
    #
    cltr
    wbr
    @39
    @32
    @17
    @91
    c0r
    cltr
    @8
    @9
    @12
    @13
    mulsrpr
    breq2d
    @38
    @35
    gt0srpr
    syl6bb
    sylibrd
    syl5bi
    2ecoptocl
    mpcom
end
