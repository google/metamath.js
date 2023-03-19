include "ccat.mm"
include "wcel.mm"
include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cresc.mm"
include "wi.mm"
include "cop.mm"
include "wa.mm"
include "df-br.mm"
include "funcrcl.mm"
include "sylbi.mm"
include "simpld.mm"
include "a1i.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "chom.mm"
include "cmap.mm"
include "cixp.mm"
include "ccid.mm"
include "wceq.mm"
include "cco.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "subcss1.mm"
include "fssd.mm"
include "csubc.mm"
include "subcrcl.mm"
include "syl.mm"
include "rescbas.mm"
include "feq3d.mm"
include "mpbid.mm"
include "2thd.mm"
include "adantr.mm"
include "cvv.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "adantlr.mm"
include "frn.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "subcss2.mm"
include "sstrd.mm"
include "anbi2d.mm"
include "df-f.mm"
include "3bitr4g.mm"
include "reschom.mm"
include "oveqd.mm"
include "bitrd.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "vex.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op2ndd.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "ovex.mm"
include "elmap.mm"
include "syl6bb.mm"
include "bibi12d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "ralbi.mm"
include "3anbi3d.mm"
include "elixp2.mm"
include "ffvelrnda.mm"
include "subcid.mm"
include "eqeq2d.mm"
include "rescco.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "ralbidva.mm"
include "3anbi123d.mm"
include "simpr.mm"
include "isfunc.mm"
include "subccat.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem funcres2b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  assume funcres2b.a: |- A = ( Base ` C )
  assume funcres2b.h: |- H = ( Hom ` C )
  assume funcres2b.r: |- ( ph -> R e. ( Subcat ` D ) )
  assume funcres2b.s: |- ( ph -> R Fn ( S X. S ) )
  assume funcres2b.1: |- ( ph -> F : A --> S )
  assume funcres2b.2: |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> ( x G y ) : Y --> ( ( F ` x ) R ( F ` y ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint R x
  disjoint R y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint C f
  disjoint C g
  disjoint C z
  disjoint D f
  disjoint D g
  disjoint D z
  disjoint f ph
  disjoint g ph
  disjoint ph z
  disjoint F f
  disjoint F g
  disjoint F z
  disjoint G f
  disjoint G g
  disjoint G z
  disjoint H f
  disjoint H g
  disjoint H z
  disjoint R f
  disjoint R g
  disjoint R z
  assert |- ( ph -> ( F ( C Func D ) G <-> F ( C Func ( D |`cat R ) ) G ) )

  proof
    wph
    cC
    ccat
    wcel
    #
    cF
    cG
    cC
    cD
    cfunc
    co
    #
    wbr
    #
    cF
    cG
    cC
    cD
    cR
    cresc
    co
    #
    cfunc
    co
    #
    wbr
    #
    @2
    @0
    wi
    wph
    @2
    @0
    cD
    ccat
    wcel
    #
    @2
    cF
    cG
    cop
    #
    @1
    wcel
    @0
    @6
    wa
    cF
    cG
    @1
    df-br
    cC
    cD
    @7
    funcrcl
    sylbi
    simpld
    a1i
    @5
    @0
    wi
    wph
    @5
    @0
    @3
    ccat
    wcel
    #
    @5
    @7
    @4
    wcel
    @0
    @8
    wa
    cF
    cG
    @4
    df-br
    cC
    @3
    @7
    funcrcl
    sylbi
    simpld
    a1i
    wph
    @0
    @2
    @5
    wb
    wph
    @0
    wa
    #
    cA
    cD
    cbs
    cfv
    #
    cF
    wf
    #
    cG
    vz
    cA
    cA
    cxp
    #
    vz
    cv
    #
    c1st
    cfv
    #
    cF
    cfv
    #
    @13
    c2nd
    cfv
    #
    cF
    cfv
    #
    cD
    chom
    cfv
    #
    co
    #
    @13
    cH
    cfv
    #
    cmap
    co
    #
    cixp
    wcel
    #
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    @23
    @23
    cG
    co
    cfv
    #
    @23
    cF
    cfv
    #
    cD
    ccid
    cfv
    #
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
    @23
    vy
    cv
    #
    cop
    #
    @13
    cC
    cco
    cfv
    #
    co
    co
    @23
    @13
    cG
    co
    cfv
    #
    @30
    @32
    @13
    cG
    co
    cfv
    #
    @31
    @23
    @32
    cG
    co
    #
    cfv
    #
    @26
    @32
    cF
    cfv
    #
    cop
    #
    @13
    cF
    cfv
    #
    cD
    cco
    cfv
    #
    co
    #
    co
    #
    wceq
    #
    vg
    @32
    @13
    cH
    co
    #
    wral
    vf
    @23
    @32
    cH
    co
    #
    wral
    #
    vz
    cA
    wral
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wral
    #
    w3a
    cA
    @3
    cbs
    cfv
    #
    cF
    wf
    #
    cG
    vz
    @12
    @15
    @17
    @3
    chom
    cfv
    #
    co
    #
    @20
    cmap
    co
    #
    cixp
    wcel
    #
    @25
    @26
    @3
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    @35
    @36
    @38
    @40
    @41
    @3
    cco
    cfv
    #
    co
    #
    co
    #
    wceq
    #
    vg
    @46
    wral
    vf
    @47
    wral
    #
    vz
    cA
    wral
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wral
    #
    w3a
    @2
    @5
    @9
    @11
    @53
    @22
    @57
    @51
    @68
    wph
    @11
    @53
    wb
    @0
    wph
    @11
    @53
    wph
    cA
    cS
    @10
    cF
    funcres2b.1
    wph
    @10
    cD
    cS
    cR
    funcres2b.r
    funcres2b.s
    @10
    eqid
    #
    subcss1
    #
    fssd
    wph
    cA
    cS
    cF
    wf
    #
    @53
    funcres2b.1
    wph
    cS
    @52
    cF
    cA
    wph
    @10
    cD
    @3
    cS
    cR
    ccat
    @3
    eqid
    #
    @69
    wph
    cR
    cD
    csubc
    cfv
    wcel
    #
    @6
    funcres2b.r
    cD
    cR
    subcrcl
    syl
    #
    funcres2b.s
    @70
    rescbas
    feq3d
    mpbid
    2thd
    adantr
    @9
    cG
    cvv
    wcel
    #
    cG
    @12
    wfn
    #
    @13
    cG
    cfv
    #
    @21
    wcel
    #
    vz
    @12
    wral
    #
    w3a
    @75
    @76
    @77
    @56
    wcel
    #
    vz
    @12
    wral
    #
    w3a
    @22
    @57
    @9
    @79
    @81
    @75
    @76
    @9
    @78
    @80
    wb
    #
    vz
    @12
    wral
    #
    @79
    @81
    wb
    @9
    @47
    @26
    @39
    @18
    co
    #
    @37
    wf
    #
    @47
    @26
    @39
    @54
    co
    #
    @37
    wf
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @83
    @9
    @88
    vx
    vy
    cA
    cA
    @9
    @23
    cA
    wcel
    #
    @32
    cA
    wcel
    #
    wa
    #
    wa
    #
    @85
    @47
    @26
    @39
    cR
    co
    #
    @37
    wf
    #
    @87
    @92
    @37
    @47
    wfn
    #
    @37
    crn
    #
    @84
    wss
    #
    wa
    @95
    @96
    @93
    wss
    #
    wa
    @85
    @94
    @92
    @97
    @98
    @95
    @92
    @97
    @98
    @92
    @96
    @93
    @84
    @92
    cY
    @93
    @37
    wf
    #
    @98
    wph
    @91
    @99
    @0
    funcres2b.2
    adantlr
    cY
    @93
    @37
    frn
    syl
    #
    @92
    cD
    cS
    @18
    cR
    @26
    @39
    wph
    @73
    @0
    @91
    funcres2b.r
    ad2antrr
    wph
    cR
    cS
    cS
    cxp
    wfn
    #
    @0
    @91
    funcres2b.s
    ad2antrr
    @18
    eqid
    #
    @92
    cA
    cS
    @23
    cF
    wph
    @71
    @0
    @91
    funcres2b.1
    ad2antrr
    #
    @9
    @89
    @90
    simprl
    ffvelrnd
    @92
    cA
    cS
    @32
    cF
    @103
    @9
    @89
    @90
    simprr
    ffvelrnd
    subcss2
    sstrd
    @100
    2thd
    anbi2d
    @47
    @84
    @37
    df-f
    @47
    @93
    @37
    df-f
    3bitr4g
    @92
    @93
    @86
    @37
    @47
    @92
    cR
    @54
    @26
    @39
    wph
    cR
    @54
    wceq
    @0
    @91
    wph
    @10
    cD
    @3
    cS
    cR
    ccat
    @72
    @69
    @74
    funcres2b.s
    @70
    reschom
    ad2antrr
    oveqd
    feq3d
    bitrd
    ralrimivva
    @82
    @88
    vz
    vx
    vy
    cA
    cA
    @13
    @33
    wceq
    #
    @78
    @85
    @80
    @87
    @104
    @78
    @37
    @84
    @47
    cmap
    co
    #
    wcel
    @85
    @104
    @77
    @37
    @21
    @105
    @104
    @77
    @33
    cG
    cfv
    @37
    @13
    @33
    cG
    fveq2
    @23
    @32
    cG
    df-ov
    syl6eqr
    #
    @104
    @19
    @84
    @20
    @47
    cmap
    @104
    @15
    @26
    @17
    @39
    @18
    @104
    @14
    @23
    cF
    @23
    @32
    @13
    vx
    vex
    #
    vy
    vex
    #
    op1std
    fveq2d
    #
    @104
    @16
    @32
    cF
    @23
    @32
    @13
    @107
    @108
    op2ndd
    fveq2d
    #
    oveq12d
    @104
    @20
    @33
    cH
    cfv
    @47
    @13
    @33
    cH
    fveq2
    @23
    @32
    cH
    df-ov
    syl6eqr
    #
    oveq12d
    eleq12d
    @84
    @47
    @37
    @26
    @39
    @18
    ovex
    @23
    @32
    cH
    ovex
    #
    elmap
    syl6bb
    @104
    @80
    @37
    @86
    @47
    cmap
    co
    #
    wcel
    @87
    @104
    @77
    @37
    @56
    @113
    @106
    @104
    @55
    @86
    @20
    @47
    cmap
    @104
    @15
    @26
    @17
    @39
    @54
    @109
    @110
    oveq12d
    @111
    oveq12d
    eleq12d
    @86
    @47
    @37
    @26
    @39
    @54
    ovex
    @112
    elmap
    syl6bb
    bibi12d
    ralxp
    sylibr
    @78
    @80
    vz
    @12
    ralbi
    syl
    3anbi3d
    vz
    @12
    @21
    cG
    elixp2
    vz
    @12
    @56
    cG
    elixp2
    3bitr4g
    @9
    @50
    @67
    vx
    cA
    @9
    @89
    wa
    #
    @29
    @60
    @49
    @66
    @114
    @28
    @59
    @25
    @114
    cD
    @3
    cS
    @27
    cR
    @26
    @72
    wph
    @73
    @0
    @89
    funcres2b.r
    ad2antrr
    wph
    @101
    @0
    @89
    funcres2b.s
    ad2antrr
    @27
    eqid
    #
    @9
    cA
    cS
    @23
    cF
    wph
    @71
    @0
    funcres2b.1
    adantr
    ffvelrnda
    subcid
    eqeq2d
    @114
    @48
    @65
    vy
    vz
    cA
    cA
    @114
    @45
    @64
    vf
    vg
    @47
    @46
    @114
    @44
    @63
    @35
    @114
    @43
    @62
    @36
    @38
    @114
    @42
    @61
    @40
    @41
    wph
    @42
    @61
    wceq
    @0
    @89
    wph
    @10
    cD
    @3
    cS
    @42
    cR
    ccat
    @72
    @69
    @74
    funcres2b.s
    @70
    @42
    eqid
    #
    rescco
    ad2antrr
    oveqd
    oveqd
    eqeq2d
    2ralbidv
    2ralbidv
    anbi12d
    ralbidva
    3anbi123d
    @9
    vx
    vy
    vz
    cA
    @10
    cC
    @34
    @24
    vf
    vg
    cD
    cF
    cG
    cH
    @27
    @18
    @42
    funcres2b.a
    @69
    funcres2b.h
    @102
    @24
    eqid
    #
    @115
    @34
    eqid
    #
    @116
    wph
    @0
    simpr
    #
    wph
    @6
    @0
    @74
    adantr
    isfunc
    @9
    vx
    vy
    vz
    cA
    @52
    cC
    @34
    @24
    vf
    vg
    @3
    cF
    cG
    cH
    @58
    @54
    @61
    funcres2b.a
    @52
    eqid
    funcres2b.h
    @54
    eqid
    @117
    @58
    eqid
    @118
    @61
    eqid
    @119
    wph
    @8
    @0
    wph
    cD
    @3
    cR
    @72
    funcres2b.r
    subccat
    adantr
    isfunc
    3bitr4d
    ex
    pm5.21ndd
end
