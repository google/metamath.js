include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "wss.mm"
include "cvsca.mm"
include "csn.mm"
include "cdif.mm"
include "clspn.mm"
include "wn.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "wrex.mm"
include "wo.mm"
include "weq.mm"
include "cminusg.mm"
include "cif.mm"
include "cmpt.mm"
include "w3a.mm"
include "simpr.mm"
include "anim2i.mm"
include "ancomd.mm"
include "ad2antrr.mm"
include "eldifi.mm"
include "adantl.mm"
include "adantr.mm"
include "simprl.mm"
include "3jca.mm"
include "simprrl.mm"
include "eqid.mm"
include "lincext2.mm"
include "syl3anc.mm"
include "lincext1.mm"
include "syl2anc.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "exp4a.mm"
include "mpid.mm"
include "simprr.mm"
include "lincext3.mm"
include "fveq2.mm"
include "cvv.mm"
include "eqidd.mm"
include "iftrue.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpinvnzcl.mm"
include "eldif.mm"
include "fvex.mm"
include "elsn.mm"
include "pm2.21.mm"
include "com25.mm"
include "sylnbi.mm"
include "sylbi.mm"
include "ex.mm"
include "com24.mm"
include "impcom.mm"
include "com13.mm"
include "imp.mm"
include "sylbid.mm"
include "syld.mm"
include "embantd.mm"
include "syldc.mm"
include "expd.mm"
include "exp4c.mm"
include "expdimp.mm"
include "pm2.01d.mm"
include "olcd.mm"
include "simpl.mm"
include "orcd.mm"
include "pm2.61ian.mm"
include "ralrimiva.mm"
include "ralnex.mm"
include "ianor.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "sylibr.mm"
include "intnand.mm"
include "clinco.mm"
include "wb.mm"
include "ssdifssd.mm"
include "difexg.mm"
include "elpwg.mm"
include "mpbird.mm"
include "lspeqlco.mm"
include "eleq2d.mm"
include "bicomd.mm"
include "jca.mm"
include "c0g.mm"
include "lcoval.mm"
include "eqcomi.mm"
include "breq2i.mm"
include "anbi1i.mm"
include "rexbii.mm"
include "anbi2i.mm"
include "syl6bb.mm"
include "bitrd.mm"
include "mtbird.mm"
include "ralrimivva.mm"

theorem lindslinindsimp1
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cM: class M
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vg: setvar g
  let vz: setvar z
  let vk: setvar k
  assume lindslinind.r: |- R = ( Scalar ` M )
  assume lindslinind.b: |- B = ( Base ` R )
  assume lindslinind.0: |- .0. = ( 0g ` R )
  assume lindslinind.z: |- Z = ( 0g ` M )

  disjoint B f
  disjoint B s
  disjoint B y
  disjoint f s
  disjoint f y
  disjoint s y
  disjoint M f
  disjoint M s
  disjoint M y
  disjoint R f
  disjoint R x
  disjoint f x
  disjoint S f
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint s x
  disjoint x y
  disjoint V s
  disjoint V y
  disjoint Z f
  disjoint Z s
  disjoint Z y
  disjoint .0. f
  disjoint .0. s
  disjoint .0. x
  disjoint .0. y
  disjoint B g
  disjoint B z
  disjoint f g
  disjoint f z
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint s z
  disjoint y z
  disjoint M g
  disjoint M z
  disjoint R z
  disjoint x z
  disjoint S g
  disjoint S z
  disjoint g x
  disjoint V g
  disjoint V z
  disjoint Z g
  disjoint .0. g
  disjoint .0. z
  disjoint k x
  assert |- ( ( S e. V /\ M e. LMod ) -> ( ( S e. ~P ( Base ` M ) /\ A. f e. ( B ^m S ) ( ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z ) -> A. x e. S ( f ` x ) = .0. ) ) -> ( S C_ ( Base ` M ) /\ A. s e. S A. y e. ( B \ { .0. } ) -. ( y ( .s ` M ) s ) e. ( ( LSpan ` M ) ` ( S \ { s } ) ) ) ) )

  proof
    cS
    cV
    wcel
    #
    cM
    clmod
    wcel
    #
    wa
    #
    cS
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @6
    cS
    cM
    clinc
    cfv
    #
    co
    #
    cZ
    wceq
    #
    wa
    #
    vx
    cv
    #
    @6
    cfv
    #
    c.0
    wceq
    #
    vx
    cS
    wral
    #
    wi
    #
    vf
    cB
    cS
    cmap
    co
    #
    wral
    #
    wa
    #
    cS
    @3
    wss
    #
    vy
    cv
    #
    vs
    cv
    #
    cM
    cvsca
    cfv
    co
    #
    cS
    @22
    csn
    #
    cdif
    #
    cM
    clspn
    cfv
    cfv
    #
    wcel
    #
    wn
    #
    vy
    cB
    c.0
    csn
    #
    cdif
    #
    wral
    vs
    cS
    wral
    #
    wa
    @2
    @19
    wa
    #
    @20
    @31
    @5
    @20
    @2
    @18
    cS
    @3
    elpwi
    #
    ad2antrl
    @32
    @28
    vs
    vy
    cS
    @30
    @32
    @22
    cS
    wcel
    #
    @21
    @30
    wcel
    #
    wa
    #
    wa
    #
    @27
    @23
    @3
    wcel
    #
    vg
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @23
    @39
    @25
    @8
    co
    wceq
    #
    wa
    #
    vg
    cB
    @25
    cmap
    co
    #
    wrex
    #
    wa
    #
    @37
    @44
    @38
    @37
    @40
    wn
    #
    @41
    wn
    #
    wo
    #
    vg
    @43
    wral
    #
    @44
    wn
    #
    @37
    @48
    vg
    @43
    @40
    @37
    @39
    @43
    wcel
    #
    wa
    #
    @48
    @40
    @52
    wa
    #
    @47
    @46
    @53
    @41
    @52
    @40
    @41
    @47
    wi
    @52
    @40
    @41
    @47
    @37
    @51
    @42
    @47
    @32
    @36
    @51
    @42
    wa
    #
    @47
    wi
    #
    @19
    @2
    @36
    @55
    wi
    #
    @18
    @5
    @2
    @56
    wi
    @18
    @5
    @2
    @36
    @55
    @18
    @5
    @2
    wa
    #
    @36
    wa
    #
    @54
    @47
    @58
    @54
    wa
    #
    @18
    vz
    cS
    vz
    vs
    weq
    #
    @21
    cR
    cminusg
    cfv
    #
    cfv
    #
    vz
    cv
    @39
    cfv
    #
    cif
    #
    cmpt
    #
    cS
    @8
    co
    #
    cZ
    wceq
    #
    @12
    @65
    cfv
    #
    c.0
    wceq
    #
    vx
    cS
    wral
    #
    wi
    #
    @47
    @59
    @18
    @65
    c.0
    cfsupp
    wbr
    #
    @71
    @59
    @1
    @5
    wa
    #
    @21
    cB
    wcel
    #
    @34
    @51
    w3a
    #
    @40
    @72
    @57
    @73
    @36
    @54
    @57
    @5
    @1
    @2
    @1
    @5
    @0
    @1
    simpr
    #
    anim2i
    #
    ancomd
    ad2antrr
    #
    @59
    @74
    @34
    @51
    @58
    @74
    @54
    @36
    @74
    @57
    @35
    @74
    @34
    @21
    cB
    @29
    eldifi
    adantl
    adantl
    adantr
    @58
    @34
    @54
    @57
    @34
    @35
    simprl
    #
    adantr
    #
    @58
    @51
    @42
    simprl
    3jca
    #
    @58
    @51
    @40
    @41
    simprrl
    vz
    @3
    cR
    cS
    cB
    @65
    @39
    cM
    @61
    @22
    @21
    c.0
    cZ
    @3
    eqid
    #
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lindslinind.z
    @61
    eqid
    #
    @65
    eqid
    #
    lincext2
    syl3anc
    @59
    @18
    @72
    @67
    @70
    @59
    @65
    @17
    wcel
    #
    @18
    @72
    @67
    wa
    #
    @70
    wi
    #
    wi
    @59
    @73
    @75
    @85
    @58
    @73
    @54
    @58
    @5
    @1
    @57
    @5
    @1
    wa
    @36
    @77
    adantr
    ancomd
    adantr
    @81
    vz
    @3
    cR
    cS
    cB
    @65
    @39
    cM
    @61
    @22
    @21
    c.0
    cZ
    @82
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lindslinind.z
    @83
    @84
    lincext1
    syl2anc
    @16
    @87
    vf
    @65
    @17
    @6
    @65
    wceq
    #
    @11
    @86
    @15
    @70
    @88
    @7
    @72
    @10
    @67
    @6
    @65
    c.0
    cfsupp
    breq1
    @88
    @9
    @66
    cZ
    @6
    @65
    cS
    @8
    oveq1
    eqeq1d
    anbi12d
    @88
    @14
    @69
    vx
    cS
    @88
    @13
    @68
    c.0
    @12
    @6
    @65
    fveq1
    eqeq1d
    ralbidv
    imbi12d
    rspcv
    syl
    exp4a
    mpid
    @59
    @67
    @70
    @47
    @59
    @73
    @75
    @42
    @67
    @78
    @81
    @58
    @51
    @42
    simprr
    vz
    @3
    cR
    cS
    cB
    @65
    @39
    cM
    @61
    @22
    @21
    c.0
    cZ
    @82
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lindslinind.z
    @83
    @84
    lincext3
    syl3anc
    @59
    @70
    @22
    @65
    cfv
    #
    c.0
    wceq
    #
    @47
    @59
    @34
    @70
    @90
    wi
    @80
    @69
    @90
    vx
    @22
    cS
    vx
    vs
    weq
    @68
    @89
    c.0
    @12
    @22
    @65
    fveq2
    eqeq1d
    rspcv
    syl
    @59
    @90
    @62
    c.0
    wceq
    #
    @47
    @59
    @89
    @62
    c.0
    @58
    @89
    @62
    wceq
    @54
    @58
    vz
    @22
    @64
    @62
    cS
    @65
    cvv
    @58
    @65
    eqidd
    @60
    @64
    @62
    wceq
    @58
    @60
    @62
    @63
    iftrue
    adantl
    @79
    @58
    @21
    @61
    fvexd
    fvmptd
    adantr
    eqeq1d
    @58
    @91
    @47
    wi
    #
    @54
    @36
    @57
    @92
    @34
    @35
    @57
    @92
    wi
    @57
    @35
    @34
    @92
    @2
    @5
    @35
    @34
    @92
    wi
    #
    wi
    #
    @1
    @0
    @5
    @94
    wi
    @1
    @35
    @5
    @0
    @93
    @1
    cR
    cgrp
    wcel
    #
    @35
    @5
    @0
    @93
    wi
    wi
    #
    wi
    cR
    cM
    lindslinind.r
    lmodfgrp
    @95
    @35
    @96
    @95
    @35
    wa
    @62
    @30
    wcel
    #
    @96
    cB
    cR
    @61
    @21
    c.0
    lindslinind.b
    lindslinind.0
    @83
    grpinvnzcl
    @97
    @62
    cB
    wcel
    #
    @62
    @29
    wcel
    #
    wn
    #
    wa
    @96
    @62
    cB
    @29
    eldif
    @100
    @96
    @98
    @99
    @91
    @96
    @62
    c.0
    @21
    @61
    fvex
    elsn
    @91
    wn
    @91
    @0
    @34
    @5
    @47
    @91
    @0
    @34
    @5
    @47
    wi
    wi
    wi
    pm2.21
    com25
    sylnbi
    adantl
    sylbi
    syl
    ex
    syl
    com24
    impcom
    impcom
    com13
    imp
    impcom
    adantr
    sylbid
    syld
    embantd
    syldc
    expd
    exp4c
    impcom
    impcom
    imp
    expdimp
    expd
    impcom
    pm2.01d
    olcd
    @46
    @52
    wa
    @46
    @47
    @46
    @52
    simpl
    orcd
    pm2.61ian
    ralrimiva
    @50
    @42
    wn
    #
    vg
    @43
    wral
    @49
    @42
    vg
    @43
    ralnex
    @101
    @48
    vg
    @43
    @40
    @41
    ianor
    ralbii
    bitr3i
    sylibr
    intnand
    @37
    @27
    @23
    cM
    @25
    clinco
    co
    #
    wcel
    #
    @45
    @37
    @1
    @25
    @4
    wcel
    #
    @27
    @103
    wb
    @2
    @1
    @19
    @36
    @76
    ad2antrr
    @32
    @104
    @36
    @32
    @104
    @25
    @3
    wss
    #
    @5
    @105
    @2
    @18
    @5
    cS
    @3
    @24
    @33
    ssdifssd
    #
    ad2antrl
    @32
    @25
    cvv
    wcel
    #
    @104
    @105
    wb
    #
    @0
    @107
    @1
    @19
    cS
    @24
    cV
    difexg
    ad2antrr
    @25
    @3
    cvv
    elpwg
    #
    syl
    mpbird
    adantr
    @1
    @104
    wa
    #
    @103
    @27
    @110
    @102
    @26
    @23
    @3
    cM
    @25
    @82
    lspeqlco
    eleq2d
    bicomd
    syl2anc
    @37
    @110
    @103
    @45
    wb
    @32
    @110
    @36
    @32
    @1
    @104
    @2
    @1
    @19
    @76
    adantr
    @5
    @104
    @2
    @18
    @5
    @104
    @105
    @106
    @5
    @107
    @108
    cS
    @24
    @4
    difexg
    @109
    syl
    mpbird
    ad2antrl
    jca
    adantr
    @110
    @103
    @38
    @39
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @41
    wa
    #
    vg
    @43
    wrex
    #
    wa
    @45
    @3
    @23
    cB
    cR
    cM
    @25
    clmod
    vg
    @82
    lindslinind.r
    lindslinind.b
    lcoval
    @114
    @44
    @38
    @113
    @42
    vg
    @43
    @112
    @40
    @41
    @111
    c.0
    @39
    cfsupp
    c.0
    @111
    lindslinind.0
    eqcomi
    breq2i
    anbi1i
    rexbii
    anbi2i
    syl6bb
    syl
    bitrd
    mtbird
    ralrimivva
    jca
    ex
end
