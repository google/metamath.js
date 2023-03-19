include "ccat.mm"
include "wcel.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "c2nd.mm"
include "cop.mm"
include "cfunc.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "chom.mm"
include "cmpt.mm"
include "eqid.mm"
include "id.mm"
include "idfuval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "fvex.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "xpex.mm"
include "mptex.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "opeq2d.mm"
include "eqtr4d.mm"
include "wbr.mm"
include "wf.mm"
include "c1st.mm"
include "cmap.mm"
include "cixp.mm"
include "ccid.mm"
include "wceq.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "elmap.mm"
include "mpbir.mm"
include "xp1st.mm"
include "adantl.mm"
include "fvresi.mm"
include "syl.mm"
include "xp2nd.mm"
include "oveq12d.mm"
include "df-ov.mm"
include "1st2nd2.mm"
include "oveq1d.mm"
include "syl5eleqr.mm"
include "ralrimiva.mm"
include "wb.mm"
include "mptelixpg.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "simpl.mm"
include "simpr.mm"
include "catidcl.mm"
include "idfu2nd.mm"
include "fveq1d.mm"
include "3eqtr4d.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "simprr.mm"
include "catcocl.mm"
include "opeq12d.mm"
include "idfu2.mm"
include "oveq123d.mm"
include "ralrimivva.mm"
include "jca.mm"
include "isfunc.mm"
include "mpbir3and.mm"
include "df-br.mm"
include "sylib.mm"

theorem idfucl
  let cC: class C
  let cI: class I
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume idfucl.i: |- I = ( idFunc ` C )


  assert |- ( C e. Cat -> I e. ( C Func C ) )

  proof
    cC
    ccat
    wcel
    #
    cI
    cid
    cC
    cbs
    cfv
    #
    cres
    #
    cI
    c2nd
    cfv
    #
    cop
    #
    cC
    cC
    cfunc
    co
    #
    @0
    cI
    @2
    vz
    @1
    @1
    cxp
    #
    cid
    vz
    cv
    #
    cC
    chom
    cfv
    #
    cfv
    #
    cres
    #
    cmpt
    #
    cop
    #
    @4
    @0
    vz
    @1
    cC
    @8
    cI
    idfucl.i
    @1
    eqid
    #
    @0
    id
    #
    @8
    eqid
    #
    idfuval
    #
    @0
    @3
    @11
    @2
    @0
    @3
    @12
    c2nd
    cfv
    @11
    @0
    cI
    @12
    c2nd
    @16
    fveq2d
    @2
    @11
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    cC
    cbs
    fvex
    #
    @1
    cvv
    resiexg
    ax-mp
    vz
    @6
    @10
    @1
    @1
    @17
    @17
    xpex
    #
    mptex
    op2nd
    syl6eq
    #
    opeq2d
    eqtr4d
    @0
    @2
    @3
    @5
    wbr
    #
    @4
    @5
    wcel
    @0
    @20
    @1
    @1
    @2
    wf
    #
    @3
    vz
    @6
    @7
    c1st
    cfv
    #
    @2
    cfv
    #
    @7
    c2nd
    cfv
    #
    @2
    cfv
    #
    @8
    co
    #
    @9
    cmap
    co
    #
    cixp
    #
    wcel
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    #
    @29
    @29
    @3
    co
    #
    cfv
    #
    @29
    @2
    cfv
    #
    @30
    cfv
    #
    wceq
    #
    vg
    cv
    #
    vf
    cv
    #
    @29
    vy
    cv
    #
    cop
    #
    @7
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    @29
    @7
    @3
    co
    #
    cfv
    #
    @37
    @39
    @7
    @3
    co
    cfv
    #
    @38
    @29
    @39
    @3
    co
    cfv
    #
    @34
    @39
    @2
    cfv
    #
    cop
    #
    @7
    @2
    cfv
    #
    @41
    co
    #
    co
    #
    wceq
    #
    vg
    @39
    @7
    @8
    co
    #
    wral
    vf
    @29
    @39
    @8
    co
    #
    wral
    #
    vz
    @1
    wral
    vy
    @1
    wral
    #
    wa
    #
    vx
    @1
    wral
    @1
    @1
    @2
    wf1o
    @21
    @0
    @1
    f1oi
    @1
    @1
    @2
    f1of
    mp1i
    @0
    @3
    @11
    @28
    @19
    @0
    @10
    @27
    wcel
    #
    vz
    @6
    wral
    #
    @11
    @28
    wcel
    #
    @0
    @59
    vz
    @6
    @0
    @7
    @6
    wcel
    #
    wa
    #
    @10
    @9
    @9
    cmap
    co
    #
    @27
    @10
    @64
    wcel
    @9
    @9
    @10
    wf
    #
    @9
    @9
    @10
    wf1o
    @65
    @9
    f1oi
    @9
    @9
    @10
    f1of
    ax-mp
    @9
    @9
    @10
    @7
    @8
    fvex
    #
    @66
    elmap
    mpbir
    @63
    @26
    @9
    @9
    cmap
    @63
    @26
    @22
    @24
    cop
    #
    @8
    cfv
    #
    @9
    @63
    @26
    @22
    @24
    @8
    co
    @68
    @63
    @23
    @22
    @25
    @24
    @8
    @63
    @22
    @1
    wcel
    #
    @23
    @22
    wceq
    @62
    @69
    @0
    @7
    @1
    @1
    xp1st
    adantl
    @1
    @22
    fvresi
    syl
    @63
    @24
    @1
    wcel
    #
    @25
    @24
    wceq
    @62
    @70
    @0
    @7
    @1
    @1
    xp2nd
    adantl
    @1
    @24
    fvresi
    syl
    oveq12d
    @22
    @24
    @8
    df-ov
    syl6eq
    @63
    @7
    @67
    @8
    @62
    @7
    @67
    wceq
    @0
    @7
    @1
    @1
    1st2nd2
    adantl
    fveq2d
    eqtr4d
    oveq1d
    syl5eleqr
    ralrimiva
    @6
    cvv
    wcel
    @61
    @60
    wb
    @18
    vz
    @6
    @10
    @27
    cvv
    mptelixpg
    ax-mp
    sylibr
    eqeltrd
    @0
    @58
    vx
    @1
    @0
    @29
    @1
    wcel
    #
    wa
    #
    @36
    @57
    @72
    @31
    cid
    @29
    @29
    @8
    co
    #
    cres
    #
    cfv
    #
    @31
    @33
    @35
    @72
    @31
    @73
    wcel
    @75
    @31
    wceq
    @72
    @1
    cC
    @30
    @8
    @29
    @13
    @15
    @30
    eqid
    #
    @0
    @71
    simpl
    #
    @0
    @71
    simpr
    #
    catidcl
    @73
    @31
    fvresi
    syl
    @72
    @31
    @32
    @74
    @72
    @1
    cC
    @8
    cI
    @29
    @29
    idfucl.i
    @13
    @77
    @15
    @78
    @78
    idfu2nd
    fveq1d
    @72
    @34
    @29
    @30
    @71
    @34
    @29
    wceq
    #
    @0
    @1
    @29
    fvresi
    #
    adantl
    fveq2d
    3eqtr4d
    @72
    @56
    vy
    vz
    @1
    @1
    @72
    @39
    @1
    wcel
    #
    @7
    @1
    wcel
    #
    wa
    #
    wa
    #
    @53
    vf
    vg
    @55
    @54
    @84
    @38
    @55
    wcel
    #
    @37
    @54
    wcel
    #
    wa
    #
    wa
    #
    @43
    cid
    @29
    @7
    @8
    co
    #
    cres
    #
    cfv
    #
    @43
    @45
    @52
    @88
    @43
    @89
    wcel
    @91
    @43
    wceq
    @88
    @1
    cC
    @41
    @38
    @37
    @8
    @29
    @39
    @7
    @13
    @15
    @41
    eqid
    #
    @72
    @0
    @83
    @87
    @77
    ad2antrr
    #
    @72
    @71
    @83
    @87
    @78
    ad2antrr
    #
    @72
    @81
    @82
    @87
    simplrl
    #
    @72
    @81
    @82
    @87
    simplrr
    #
    @84
    @85
    @86
    simprl
    #
    @84
    @85
    @86
    simprr
    #
    catcocl
    @89
    @43
    fvresi
    syl
    @88
    @43
    @44
    @90
    @88
    @1
    cC
    @8
    cI
    @29
    @7
    idfucl.i
    @13
    @93
    @15
    @94
    @96
    idfu2nd
    fveq1d
    @88
    @46
    @37
    @47
    @38
    @51
    @42
    @88
    @49
    @40
    @50
    @7
    @41
    @88
    @34
    @29
    @48
    @39
    @88
    @71
    @79
    @94
    @80
    syl
    @88
    @81
    @48
    @39
    wceq
    @95
    @1
    @39
    fvresi
    syl
    opeq12d
    @88
    @82
    @50
    @7
    wceq
    @96
    @1
    @7
    fvresi
    syl
    oveq12d
    @88
    @1
    cC
    @37
    @8
    cI
    @39
    @7
    idfucl.i
    @13
    @93
    @15
    @95
    @96
    @98
    idfu2
    @88
    @1
    cC
    @38
    @8
    cI
    @29
    @39
    idfucl.i
    @13
    @93
    @15
    @94
    @95
    @97
    idfu2
    oveq123d
    3eqtr4d
    ralrimivva
    ralrimivva
    jca
    ralrimiva
    @0
    vx
    vy
    vz
    @1
    @1
    cC
    @41
    @30
    vf
    vg
    cC
    @2
    @3
    @8
    @30
    @8
    @41
    @13
    @13
    @15
    @15
    @76
    @76
    @92
    @92
    @14
    @14
    isfunc
    mpbir3and
    @2
    @3
    @5
    df-br
    sylib
    eqeltrd
end
