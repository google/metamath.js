include "clmod.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cpr.mm"
include "clindeps.mm"
include "wbr.mm"
include "cv.mm"
include "cfsupp.mm"
include "clinc.mm"
include "cfv.mm"
include "wrex.mm"
include "cmap.mm"
include "cur.mm"
include "cop.mm"
include "cminusg.mm"
include "cvv.mm"
include "wf.mm"
include "3simpa.mm"
include "ad2antlr.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "simp3.mm"
include "fprg.mm"
include "syl3anc.mm"
include "cfn.mm"
include "prfi.mm"
include "c0g.mm"
include "eqeltri.mm"
include "fdmfifsupp.mm"
include "cplusg.mm"
include "anim2i.mm"
include "adantr.mm"
include "eqid.mm"
include "lmod1cl.mm"
include "simp1.mm"
include "anim12ci.mm"
include "simp2.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "simpl.mm"
include "grpinvcl.mm"
include "syl2an.mm"
include "lincvalpr.mm"
include "syl112anc.mm"
include "simpll.mm"
include "adantl.mm"
include "3jca.mm"
include "jca.mm"
include "simprr.mm"
include "ldepsprlem.mm"
include "sylc.mm"
include "eqtrd.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "crg.mm"
include "lmodring.mm"
include "eqcom.mm"
include "csn.mm"
include "01eq0ring.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "eleq2.mm"
include "elsni.mm"
include "oveq1.mm"
include "anim1i.mm"
include "ancomd.mm"
include "lmodvs1.mm"
include "syl.mm"
include "eqneqall.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "sylbid.mm"
include "ex.mm"
include "com3r.mm"
include "syl6bi.mm"
include "impd.mm"
include "com23.mm"
include "mpd.mm"
include "syl5bi.mm"
include "com25.mm"
include "mpcom.mm"
include "imp31.mm"
include "orc.mm"
include "pm2.61d1.mm"
include "eqeq2i.mm"
include "necon3abii.mm"
include "orbi1i.mm"
include "sylibr.mm"
include "fvexd.mm"
include "fvpr1g.mm"
include "neeq1d.mm"
include "fvpr2g.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "wb.mm"
include "fveq2.mm"
include "rexprg.mm"
include "cbs.mm"
include "jctir.mm"
include "mapprop.mm"
include "syl221anc.mm"
include "breq1.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "rspcedv.mm"
include "mp3and.mm"
include "cpw.mm"
include "prelpwi.mm"
include "3adant3.mm"
include "islindeps.mm"
include "syl2anc.mm"

theorem ldepspr
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cM: class M
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vk: setvar k
  assume snlindsntor.b: |- B = ( Base ` M )
  assume snlindsntor.r: |- R = ( Scalar ` M )
  assume snlindsntor.s: |- S = ( Base ` R )
  assume snlindsntor.0: |- .0. = ( 0g ` R )
  assume snlindsntor.z: |- Z = ( 0g ` M )
  assume snlindsntor.t: |- .x. = ( .s ` M )


  assert |- ( ( M e. LMod /\ ( X e. B /\ Y e. B /\ X =/= Y ) ) -> ( ( A e. S /\ X = ( A .x. Y ) ) -> { X , Y } linDepS M ) )

  proof
    cM
    clmod
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cY
    wne
    #
    w3a
    #
    wa
    #
    cA
    cS
    wcel
    #
    cX
    cA
    cY
    c.x
    co
    #
    wceq
    #
    wa
    #
    cX
    cY
    cpr
    #
    cM
    clindeps
    wbr
    #
    @5
    @9
    wa
    #
    @11
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @13
    @10
    cM
    clinc
    cfv
    #
    co
    #
    cZ
    wceq
    #
    vv
    cv
    #
    @13
    cfv
    #
    c.0
    wne
    #
    vv
    @10
    wrex
    #
    w3a
    #
    vf
    cS
    @10
    cmap
    co
    #
    wrex
    #
    @12
    cX
    cR
    cur
    cfv
    #
    cop
    cY
    cA
    cR
    cminusg
    cfv
    #
    cfv
    #
    cop
    cpr
    #
    c.0
    cfsupp
    wbr
    #
    @28
    @10
    @15
    co
    #
    cZ
    wceq
    #
    @18
    @28
    cfv
    #
    c.0
    wne
    #
    vv
    @10
    wrex
    #
    @24
    @12
    @10
    @25
    @27
    cpr
    #
    @28
    cvv
    c.0
    @12
    @1
    @2
    wa
    #
    @25
    cvv
    wcel
    #
    @27
    cvv
    wcel
    #
    wa
    #
    @3
    @10
    @35
    @28
    wf
    @4
    @36
    @0
    @9
    @1
    @2
    @3
    3simpa
    ad2antlr
    #
    @39
    @12
    @37
    @38
    cR
    cur
    fvex
    cA
    @26
    fvex
    pm3.2i
    a1i
    @4
    @3
    @0
    @9
    @1
    @2
    @3
    simp3
    #
    ad2antlr
    #
    cX
    cY
    @25
    @27
    cB
    cB
    cvv
    cvv
    fprg
    syl3anc
    @10
    cfn
    wcel
    @12
    cX
    cY
    prfi
    a1i
    c.0
    cvv
    wcel
    @12
    c.0
    cR
    c0g
    cfv
    #
    cvv
    snlindsntor.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    fdmfifsupp
    @12
    @30
    @25
    cX
    c.x
    co
    @27
    cY
    c.x
    co
    cM
    cplusg
    cfv
    #
    co
    #
    cZ
    @12
    @0
    @3
    wa
    #
    @1
    @25
    cS
    wcel
    #
    wa
    #
    @2
    @27
    cS
    wcel
    #
    @30
    @45
    wceq
    @5
    @46
    @9
    @4
    @3
    @0
    @41
    anim2i
    adantr
    @5
    @48
    @9
    @0
    @47
    @4
    @1
    @25
    cR
    cS
    cM
    snlindsntor.r
    snlindsntor.s
    @25
    eqid
    #
    lmod1cl
    #
    @1
    @2
    @3
    simp1
    #
    anim12ci
    adantr
    @4
    @2
    @0
    @9
    @1
    @2
    @3
    simp2
    #
    ad2antlr
    #
    @5
    cR
    cgrp
    wcel
    #
    @6
    @49
    @9
    @0
    @55
    @4
    cR
    cM
    snlindsntor.r
    lmodfgrp
    adantr
    @6
    @8
    simpl
    #
    cS
    cR
    @26
    cA
    snlindsntor.s
    @26
    eqid
    #
    grpinvcl
    syl2an
    #
    cB
    @44
    cS
    cR
    c.x
    @28
    cM
    cX
    cY
    @25
    @27
    snlindsntor.b
    snlindsntor.r
    snlindsntor.s
    snlindsntor.t
    @44
    eqid
    @28
    eqid
    #
    lincvalpr
    syl112anc
    @12
    @0
    @1
    @2
    @6
    w3a
    #
    wa
    @8
    @45
    cZ
    wceq
    @12
    @0
    @60
    @0
    @4
    @9
    simpll
    #
    @12
    @1
    @2
    @6
    @4
    @1
    @0
    @9
    @52
    ad2antlr
    #
    @54
    @9
    @6
    @5
    @56
    adantl
    3jca
    jca
    @5
    @6
    @8
    simprr
    cA
    cB
    cR
    cS
    c.x
    @25
    cM
    @26
    cX
    cY
    c.0
    cZ
    snlindsntor.b
    snlindsntor.r
    snlindsntor.s
    snlindsntor.0
    snlindsntor.z
    snlindsntor.t
    @50
    @57
    ldepsprlem
    sylc
    eqtrd
    @12
    @34
    cX
    @28
    cfv
    #
    c.0
    wne
    #
    cY
    @28
    cfv
    #
    c.0
    wne
    #
    wo
    #
    @12
    @67
    @25
    c.0
    wne
    #
    @27
    c.0
    wne
    #
    wo
    #
    @12
    @25
    @43
    wceq
    #
    wn
    #
    @69
    wo
    #
    @70
    @12
    @71
    @73
    @0
    @4
    @9
    @71
    @73
    wi
    #
    cR
    crg
    wcel
    #
    @0
    @4
    @9
    @74
    wi
    wi
    cR
    cM
    snlindsntor.r
    lmodring
    @75
    @71
    @4
    @9
    @0
    @73
    @71
    @43
    @25
    wceq
    #
    @75
    @4
    @9
    @0
    @73
    wi
    #
    wi
    wi
    #
    @25
    @43
    eqcom
    @75
    @76
    @78
    @75
    @76
    wa
    cS
    @43
    csn
    #
    wceq
    #
    @78
    cS
    cR
    @25
    @43
    snlindsntor.s
    @43
    eqid
    @50
    01eq0ring
    @76
    @80
    @78
    wi
    @75
    @76
    @80
    cS
    @25
    csn
    #
    wceq
    #
    @78
    @76
    @79
    @81
    cS
    @43
    @25
    sneq
    eqeq2d
    @82
    @9
    @4
    @77
    @82
    @6
    @8
    @4
    @77
    wi
    #
    @82
    @6
    cA
    @81
    wcel
    #
    @8
    @83
    wi
    #
    cS
    @81
    cA
    eleq2
    @84
    cA
    @25
    wceq
    #
    @85
    cA
    @25
    elsni
    @86
    @8
    cX
    @25
    cY
    c.x
    co
    #
    wceq
    #
    @83
    @86
    @7
    @87
    cX
    cA
    @25
    cY
    c.x
    oveq1
    eqeq2d
    @4
    @0
    @88
    @73
    @4
    @0
    @88
    @73
    wi
    @4
    @0
    wa
    #
    @88
    cX
    cY
    wceq
    #
    @73
    @89
    @87
    cY
    cX
    @89
    @0
    @2
    wa
    @87
    cY
    wceq
    @89
    @2
    @0
    @4
    @2
    @0
    @53
    anim1i
    ancomd
    c.x
    @25
    cR
    cB
    cM
    cY
    snlindsntor.b
    snlindsntor.r
    snlindsntor.t
    @50
    lmodvs1
    syl
    eqeq2d
    @4
    @90
    @73
    wi
    #
    @0
    @3
    @1
    @91
    @2
    @90
    @3
    @73
    @73
    cX
    cY
    eqneqall
    com12
    3ad2ant3
    adantr
    sylbid
    ex
    com3r
    syl6bi
    syl
    syl6bi
    impd
    com23
    syl6bi
    adantl
    mpd
    ex
    syl5bi
    com25
    mpcom
    imp31
    @72
    @69
    orc
    pm2.61d1
    @68
    @72
    @69
    @71
    @25
    c.0
    c.0
    @43
    @25
    snlindsntor.0
    eqeq2i
    necon3abii
    orbi1i
    sylibr
    @12
    @64
    @68
    @66
    @69
    @12
    @63
    @25
    c.0
    @12
    @1
    @37
    @3
    @63
    @25
    wceq
    @62
    @12
    cR
    cur
    fvexd
    @42
    cX
    cY
    @25
    @27
    cB
    cvv
    fvpr1g
    syl3anc
    neeq1d
    @12
    @65
    @27
    c.0
    @12
    @2
    @38
    @3
    @65
    @27
    wceq
    @54
    @12
    cA
    @26
    fvexd
    @42
    cX
    cY
    @25
    @27
    cB
    cvv
    fvpr2g
    syl3anc
    neeq1d
    orbi12d
    mpbird
    @12
    @36
    @34
    @67
    wb
    @40
    @33
    @64
    @66
    vv
    cX
    cY
    cB
    cB
    @18
    cX
    wceq
    @32
    @63
    c.0
    @18
    cX
    @28
    fveq2
    neeq1d
    @18
    cY
    wceq
    @32
    @65
    c.0
    @18
    cY
    @28
    fveq2
    neeq1d
    rexprg
    syl
    mpbird
    @12
    @22
    @29
    @31
    @34
    w3a
    #
    vf
    @28
    @23
    @12
    @1
    @47
    @2
    @49
    @3
    cS
    cvv
    wcel
    #
    wa
    @28
    @23
    wcel
    @62
    @5
    @47
    @9
    @0
    @47
    @4
    @51
    adantr
    adantr
    @54
    @58
    @12
    @3
    @93
    @42
    cS
    cR
    cbs
    cfv
    cvv
    snlindsntor.s
    cR
    cbs
    fvex
    eqeltri
    jctir
    @25
    @27
    cS
    @28
    cB
    cvv
    cX
    cY
    @59
    mapprop
    syl221anc
    @13
    @28
    wceq
    #
    @22
    @92
    wb
    @12
    @94
    @14
    @29
    @17
    @31
    @21
    @34
    @13
    @28
    c.0
    cfsupp
    breq1
    @94
    @16
    @30
    cZ
    @13
    @28
    @10
    @15
    oveq1
    eqeq1d
    @94
    @20
    @33
    vv
    @10
    @94
    @19
    @32
    c.0
    @18
    @13
    @28
    fveq1
    neeq1d
    rexbidv
    3anbi123d
    adantl
    rspcedv
    mp3and
    @12
    @0
    @10
    cB
    cpw
    wcel
    #
    @11
    @24
    wb
    @61
    @4
    @95
    @0
    @9
    @1
    @2
    @95
    @3
    cX
    cY
    cB
    prelpwi
    3adant3
    ad2antlr
    vv
    cB
    cR
    @10
    vf
    cS
    cM
    clmod
    c.0
    cZ
    snlindsntor.b
    snlindsntor.z
    snlindsntor.r
    snlindsntor.s
    snlindsntor.0
    islindeps
    syl2anc
    mpbird
    ex
end
