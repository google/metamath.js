include "crn.mm"
include "wwe.mm"
include "cxp.mm"
include "wss.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrn.mm"
include "simpr.mm"
include "opelxpd.mm"
include "fmptd.mm"
include "frn.mm"
include "3syl.mm"
include "wexp.mm"
include "syl2anc.mm"
include "wess.mm"
include "sylc.mm"
include "ccnv.mm"
include "wiso.mm"
include "cima.mm"
include "cvv.mm"
include "wal.mm"
include "wi.mm"
include "wf1o.mm"
include "wf1.mm"
include "wceq.mm"
include "weq.mm"
include "wral.mm"
include "fveq2.mm"
include "id.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "eqeqan12d.mm"
include "fvex.mm"
include "vex.mm"
include "opth.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "rgen2a.mm"
include "dff13.mm"
include "sylanblrc.mm"
include "f1f1orn.mm"
include "f1ocnv.mm"
include "4syl.mm"
include "wbr.mm"
include "copab.mm"
include "eqid.mm"
include "f1oiso2.mm"
include "wb.mm"
include "wo.mm"
include "wrel.mm"
include "frel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "fveq1d.mm"
include "breq12d.mm"
include "syl.mm"
include "adantr.mm"
include "breqan12d.mm"
include "adantl.mm"
include "jca.mm"
include "anim12dan.mm"
include "biantrurd.mm"
include "c1st.mm"
include "c2nd.mm"
include "eleq1.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "op1std.mm"
include "breq1d.mm"
include "eqeq1d.mm"
include "op2ndd.mm"
include "anbi12d.mm"
include "orbi12d.mm"
include "anbi2d.mm"
include "breq2d.mm"
include "eqeq2d.mm"
include "brab.mm"
include "syl6rbbr.mm"
include "3bitrrd.mm"
include "pm5.32da.mm"
include "opabbidv.mm"
include "syl5eq.mm"
include "isoeq3.mm"
include "syl5ibr.mm"
include "isocnv.mm"
include "imacnvcnv.mm"
include "xpexg.mm"
include "sylancl.mm"
include "cres.mm"
include "cdm.mm"
include "imadmres.mm"
include "dmres.mm"
include "elin2.mm"
include "simprr.mm"
include "f1dm.mm"
include "eleqtrd.mm"
include "wfn.mm"
include "ffnd.mm"
include "cin.mm"
include "inss2.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "syl5eqss.mm"
include "simprl.mm"
include "eleqtrrd.mm"
include "sylanbrc.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "syl6eleq.mm"
include "eqeltrd.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "f1fun.mm"
include "resss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "funimass4.mm"
include "mpbird.mm"
include "syl5eqssr.mm"
include "ssexd.mm"
include "syl5eqel.mm"
include "alrimiv.mm"
include "isowe2.mm"
include "mpd.mm"

theorem fnwelem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  assume fnwe.1: |- T = { <. x , y >. | ( ( x e. A /\ y e. A ) /\ ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x S y ) ) ) }
  assume fnwe.2: |- ( ph -> F : A --> B )
  assume fnwe.3: |- ( ph -> R We B )
  assume fnwe.4: |- ( ph -> S We A )
  assume fnwe.5: |- ( ph -> ( F " w ) e. _V )
  assume fnwelem.6: |- Q = { <. u , v >. | ( ( u e. ( B X. A ) /\ v e. ( B X. A ) ) /\ ( ( 1st ` u ) R ( 1st ` v ) \/ ( ( 1st ` u ) = ( 1st ` v ) /\ ( 2nd ` u ) S ( 2nd ` v ) ) ) ) }
  assume fnwelem.7: |- G = ( z e. A |-> <. ( F ` z ) , z >. )

  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint ph w
  disjoint ph x
  disjoint ph z
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint T w
  assert |- ( ph -> T We A )

  proof
    wph
    cG
    crn
    #
    cQ
    wwe
    #
    cA
    cT
    wwe
    #
    wph
    @0
    cB
    cA
    cxp
    #
    wss
    #
    @3
    cQ
    wwe
    #
    @1
    wph
    cA
    cB
    cF
    wf
    #
    cA
    @3
    cG
    wf
    #
    @4
    fnwe.2
    @6
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    @8
    cop
    #
    @3
    cG
    @6
    @8
    cA
    wcel
    #
    wa
    @9
    @8
    cB
    cA
    cA
    cB
    @8
    cF
    ffvelrn
    @6
    @11
    simpr
    opelxpd
    fnwelem.7
    fmptd
    #
    cA
    @3
    cG
    frn
    3syl
    wph
    cB
    cR
    wwe
    cA
    cS
    wwe
    @5
    fnwe.3
    fnwe.4
    vu
    vv
    cB
    cA
    cR
    cS
    cQ
    fnwelem.6
    wexp
    syl2anc
    @0
    @3
    cQ
    wess
    sylc
    wph
    cA
    @0
    cT
    cQ
    cG
    ccnv
    #
    ccnv
    #
    wiso
    #
    @14
    vw
    cv
    #
    cima
    #
    cvv
    wcel
    #
    vw
    wal
    @1
    @2
    wi
    wph
    @0
    cA
    cQ
    cT
    @13
    wiso
    #
    @15
    wph
    @6
    @0
    cA
    @13
    wf1o
    #
    @19
    fnwe.2
    wph
    @6
    cA
    @3
    cG
    wf1
    #
    cA
    @0
    cG
    wf1o
    @20
    fnwe.2
    @6
    @7
    vx
    cv
    #
    cG
    cfv
    #
    vy
    cv
    #
    cG
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @21
    @12
    @28
    vx
    vy
    cA
    @22
    cA
    wcel
    #
    @24
    cA
    wcel
    #
    wa
    #
    @26
    @22
    cF
    cfv
    #
    @22
    cop
    #
    @24
    cF
    cfv
    #
    @24
    cop
    #
    wceq
    #
    @27
    @29
    @30
    @23
    @33
    @25
    @35
    vz
    @22
    @10
    @33
    cA
    cG
    vz
    vx
    weq
    #
    @9
    @32
    @8
    @22
    @8
    @22
    cF
    fveq2
    @37
    id
    opeq12d
    fnwelem.7
    @32
    @22
    opex
    #
    fvmpt
    #
    vz
    @24
    @10
    @35
    cA
    cG
    vz
    vy
    weq
    #
    @9
    @34
    @8
    @24
    @8
    @24
    cF
    fveq2
    @40
    id
    opeq12d
    fnwelem.7
    @34
    @24
    opex
    #
    fvmpt
    #
    eqeqan12d
    @36
    @32
    @34
    wceq
    #
    @27
    @32
    @22
    @34
    @24
    @22
    cF
    fvex
    #
    vx
    vex
    #
    opth
    simprbi
    syl6bi
    rgen2a
    vx
    vy
    cA
    @3
    cG
    dff13
    sylanblrc
    #
    cA
    @3
    cG
    f1f1orn
    cA
    @0
    cG
    f1ocnv
    4syl
    @20
    @19
    @6
    @0
    cA
    cQ
    @31
    @22
    @14
    cfv
    #
    @24
    @14
    cfv
    #
    cQ
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    @13
    wiso
    #
    vx
    vy
    @0
    cA
    cQ
    @51
    @13
    @51
    eqid
    f1oiso2
    @6
    cT
    @51
    wceq
    @19
    @52
    wb
    @6
    cT
    @31
    @32
    @34
    cR
    wbr
    #
    @43
    @22
    @24
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    vx
    vy
    copab
    @51
    fnwe.1
    @6
    @57
    @50
    vx
    vy
    @6
    @31
    @56
    @49
    @6
    @31
    wa
    #
    @49
    @23
    @25
    cQ
    wbr
    #
    @33
    @35
    cQ
    wbr
    #
    @56
    @6
    @49
    @59
    wb
    #
    @31
    @6
    @7
    @61
    @12
    @7
    @47
    @23
    @48
    @25
    cQ
    @7
    @22
    @14
    cG
    @7
    cG
    wrel
    @14
    cG
    wceq
    cA
    @3
    cG
    frel
    cG
    dfrel2
    sylib
    #
    fveq1d
    @7
    @24
    @14
    cG
    @62
    fveq1d
    breq12d
    syl
    adantr
    @31
    @59
    @60
    wb
    @6
    @29
    @30
    @23
    @33
    @25
    @35
    cQ
    @39
    @42
    breqan12d
    adantl
    @58
    @56
    @32
    cB
    wcel
    #
    @29
    wa
    #
    @34
    cB
    wcel
    #
    @30
    wa
    #
    wa
    #
    @56
    wa
    #
    @60
    @58
    @67
    @56
    @6
    @29
    @64
    @30
    @66
    @6
    @29
    wa
    @63
    @29
    cA
    cB
    @22
    cF
    ffvelrn
    @6
    @29
    simpr
    jca
    @6
    @30
    wa
    @65
    @30
    cA
    cB
    @24
    cF
    ffvelrn
    @6
    @30
    simpr
    jca
    anim12dan
    biantrurd
    vu
    cv
    #
    @3
    wcel
    #
    vv
    cv
    #
    @3
    wcel
    #
    wa
    #
    @69
    c1st
    cfv
    #
    @71
    c1st
    cfv
    #
    cR
    wbr
    #
    @74
    @75
    wceq
    #
    @69
    c2nd
    cfv
    #
    @71
    c2nd
    cfv
    #
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    @64
    @72
    wa
    #
    @32
    @75
    cR
    wbr
    #
    @32
    @75
    wceq
    #
    @22
    @79
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    @68
    vu
    vv
    @33
    @35
    cQ
    @38
    @41
    @69
    @33
    wceq
    #
    @73
    @83
    @82
    @88
    @89
    @70
    @64
    @72
    @89
    @70
    @33
    @3
    wcel
    @64
    @69
    @33
    @3
    eleq1
    @32
    @22
    cB
    cA
    opelxp
    syl6bb
    anbi1d
    @89
    @76
    @84
    @81
    @87
    @89
    @74
    @32
    @75
    cR
    @32
    @22
    @69
    @44
    @45
    op1std
    #
    breq1d
    @89
    @77
    @85
    @80
    @86
    @89
    @74
    @32
    @75
    @90
    eqeq1d
    @89
    @78
    @22
    @79
    cS
    @32
    @22
    @69
    @44
    @45
    op2ndd
    breq1d
    anbi12d
    orbi12d
    anbi12d
    @71
    @35
    wceq
    #
    @83
    @67
    @88
    @56
    @91
    @72
    @66
    @64
    @91
    @72
    @35
    @3
    wcel
    @66
    @71
    @35
    @3
    eleq1
    @34
    @24
    cB
    cA
    opelxp
    syl6bb
    anbi2d
    @91
    @84
    @53
    @87
    @55
    @91
    @75
    @34
    @32
    cR
    @34
    @24
    @71
    @24
    cF
    fvex
    #
    vy
    vex
    #
    op1std
    #
    breq2d
    @91
    @85
    @43
    @86
    @54
    @91
    @75
    @34
    @32
    @94
    eqeq2d
    @91
    @79
    @24
    @22
    cS
    @34
    @24
    @71
    @92
    @93
    op2ndd
    breq2d
    anbi12d
    orbi12d
    anbi12d
    fnwelem.6
    brab
    syl6rbbr
    3bitrrd
    pm5.32da
    opabbidv
    syl5eq
    @0
    cA
    cQ
    cT
    @51
    @13
    isoeq3
    syl
    syl5ibr
    sylc
    @0
    cA
    cQ
    cT
    @13
    isocnv
    syl
    wph
    @18
    vw
    wph
    @17
    cG
    @16
    cima
    #
    cvv
    cG
    @16
    imacnvcnv
    wph
    @95
    cF
    @16
    cima
    #
    @16
    cxp
    #
    cvv
    wph
    @96
    cvv
    wcel
    @16
    cvv
    wcel
    @97
    cvv
    wcel
    fnwe.5
    vw
    vex
    @96
    @16
    cvv
    cvv
    xpexg
    sylancl
    wph
    @95
    cG
    cG
    @16
    cres
    #
    cdm
    #
    cima
    #
    @97
    cG
    @16
    imadmres
    wph
    @100
    @97
    wss
    #
    @23
    @97
    wcel
    #
    vx
    @99
    wral
    #
    wph
    @102
    vx
    @99
    @22
    @99
    wcel
    wph
    @22
    @16
    wcel
    #
    @22
    cG
    cdm
    #
    wcel
    #
    wa
    #
    @102
    @22
    @16
    @105
    @99
    cG
    @16
    dmres
    elin2
    wph
    @107
    wa
    #
    @23
    @33
    @97
    @108
    @29
    @23
    @33
    wceq
    @108
    @22
    @105
    cA
    wph
    @104
    @106
    simprr
    wph
    @105
    cA
    wceq
    #
    @107
    wph
    @6
    @21
    @109
    fnwe.2
    @46
    cA
    @3
    cG
    f1dm
    3syl
    adantr
    eleqtrd
    #
    @39
    syl
    @108
    @32
    @22
    @96
    @16
    @108
    @32
    cF
    cF
    @16
    cres
    cdm
    #
    cima
    #
    @96
    @108
    cF
    cA
    wfn
    #
    @111
    cA
    wss
    @22
    @111
    wcel
    #
    @32
    @112
    wcel
    wph
    @113
    @107
    wph
    cA
    cB
    cF
    fnwe.2
    ffnd
    adantr
    #
    @108
    @111
    @16
    cF
    cdm
    #
    cin
    #
    cA
    cF
    @16
    dmres
    #
    @108
    @116
    @117
    cA
    @16
    @116
    inss2
    @108
    @113
    @116
    cA
    wceq
    @115
    cA
    cF
    fndm
    syl
    #
    syl5sseq
    syl5eqss
    @108
    @104
    @22
    @116
    wcel
    @114
    wph
    @104
    @106
    simprl
    #
    @108
    @22
    cA
    @116
    @110
    @119
    eleqtrrd
    @22
    @16
    @116
    @111
    @118
    elin2
    sylanbrc
    cA
    @111
    cF
    @22
    fnfvima
    syl3anc
    cF
    @16
    imadmres
    syl6eleq
    @120
    opelxpd
    eqeltrd
    sylan2b
    ralrimiva
    wph
    cG
    wfun
    #
    @99
    @105
    wss
    #
    @101
    @103
    wb
    wph
    @6
    @21
    @121
    fnwe.2
    @46
    cA
    @3
    cG
    f1fun
    3syl
    @98
    cG
    wss
    @122
    cG
    @16
    resss
    @98
    cG
    dmss
    ax-mp
    vx
    @99
    @97
    cG
    funimass4
    sylancl
    mpbird
    syl5eqssr
    ssexd
    syl5eqel
    alrimiv
    vw
    cA
    @0
    cT
    cQ
    @14
    isowe2
    syl2anc
    mpd
end
