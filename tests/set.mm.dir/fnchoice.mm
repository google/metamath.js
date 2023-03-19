include "cv.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "fneq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "eqid.mm"
include "fn0.mm"
include "mpbir.mm"
include "0ex.mm"
include "fneq1.mm"
include "spcev.mm"
include "ax-mp.mm"
include "ral0.mm"
include "pm3.2i.mm"
include "exan.mm"
include "cfn.mm"
include "wn.mm"
include "cop.mm"
include "cvv.mm"
include "wf.mm"
include "dffn2.mm"
include "biimpi.mm"
include "ad2antrl.mm"
include "vex.mm"
include "a1i.mm"
include "simpllr.mm"
include "fsnunf.mm"
include "syl121anc.mm"
include "sylibr.mm"
include "simplr.mm"
include "simprr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simpr.mm"
include "adantr.mm"
include "jca.mm"
include "nelne2.mm"
include "necomd.mm"
include "syl.mm"
include "fvunsn.mm"
include "neeq1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "eleq2.mm"
include "bitrd.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "rspcv.mm"
include "syl5bir.mm"
include "syl3c.mm"
include "eqeltrd.mm"
include "simp-4l.mm"
include "w3a.mm"
include "elsni.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "eqtrd.mm"
include "simp3.mm"
include "pm2.21ddne.mm"
include "syl3anc.mm"
include "wo.mm"
include "elun.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "ex.mm"
include "ralrimi.mm"
include "syl21anc.mm"
include "eximdv.mm"
include "snex.mm"
include "unex.mm"
include "fveq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "eximi.mm"
include "syl6.mm"
include "ax5e.mm"
include "imp.mm"
include "an32s.mm"
include "cbvexv.mm"
include "neq0.mm"
include "eeanv.mm"
include "simprrl.mm"
include "simpl.mm"
include "simprrr.mm"
include "simplrl.mm"
include "cdm.mm"
include "fndm.mm"
include "neleqtrrd.mm"
include "fsnunfv.mm"
include "3eltr4d.mm"
include "2eximdv.mm"
include "exlimiv.mm"
include "pm2.61dan.mm"
include "findcard2s.mm"

theorem fnchoice
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint f g
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint f u
  disjoint u x
  disjoint u y
  disjoint A w
  disjoint A y
  disjoint A z
  assert |- ( A e. Fin -> E. f ( f Fn A /\ A. x e. A ( x =/= (/) -> ( f ` x ) e. x ) ) )

  proof
    vf
    cv
    #
    vw
    cv
    #
    wfn
    #
    vx
    cv
    #
    c0
    wne
    #
    @3
    @0
    cfv
    #
    @3
    wcel
    #
    wi
    #
    vx
    @1
    wral
    #
    wa
    #
    vf
    wex
    @0
    c0
    wfn
    #
    @7
    vx
    c0
    wral
    #
    wa
    #
    vf
    wex
    @0
    vy
    cv
    #
    wfn
    #
    @7
    vx
    @13
    wral
    #
    wa
    #
    vf
    wex
    #
    @0
    @13
    vz
    cv
    #
    csn
    #
    cun
    #
    wfn
    #
    @7
    vx
    @20
    wral
    #
    wa
    #
    vf
    wex
    #
    @0
    cA
    wfn
    #
    @7
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    vw
    vy
    vz
    cA
    @1
    c0
    wceq
    #
    @9
    @12
    vf
    @28
    @2
    @10
    @8
    @11
    @1
    c0
    @0
    fneq2
    @7
    vx
    @1
    c0
    raleq
    anbi12d
    exbidv
    @1
    @13
    wceq
    #
    @9
    @16
    vf
    @29
    @2
    @14
    @8
    @15
    @1
    @13
    @0
    fneq2
    @7
    vx
    @1
    @13
    raleq
    anbi12d
    exbidv
    @1
    @20
    wceq
    #
    @9
    @23
    vf
    @30
    @2
    @21
    @8
    @22
    @1
    @20
    @0
    fneq2
    @7
    vx
    @1
    @20
    raleq
    anbi12d
    exbidv
    @1
    cA
    wceq
    #
    @9
    @27
    vf
    @31
    @2
    @25
    @8
    @26
    @1
    cA
    @0
    fneq2
    @7
    vx
    @1
    cA
    raleq
    anbi12d
    exbidv
    @10
    @11
    vf
    @10
    vf
    wex
    #
    @11
    c0
    c0
    wfn
    #
    @32
    @33
    c0
    c0
    wceq
    c0
    eqid
    c0
    fn0
    mpbir
    @10
    @33
    vf
    c0
    0ex
    c0
    @0
    c0
    fneq1
    spcev
    ax-mp
    @7
    vx
    ral0
    pm3.2i
    exan
    @13
    cfn
    wcel
    #
    @18
    @13
    wcel
    wn
    #
    wa
    #
    @17
    @24
    @36
    @17
    wa
    #
    @18
    c0
    wceq
    #
    @24
    @37
    @38
    wa
    vg
    cv
    #
    @20
    wfn
    #
    @4
    @3
    @39
    cfv
    #
    @3
    wcel
    #
    wi
    #
    vx
    @20
    wral
    #
    wa
    #
    vg
    wex
    #
    @24
    @36
    @38
    @17
    @46
    @36
    @38
    wa
    #
    @17
    @46
    @47
    @17
    @46
    vf
    wex
    #
    @46
    @47
    @17
    @0
    @18
    @1
    cop
    #
    csn
    #
    cun
    #
    @20
    wfn
    #
    @4
    @3
    @51
    cfv
    #
    @3
    wcel
    #
    wi
    #
    vx
    @20
    wral
    #
    wa
    #
    vf
    wex
    @48
    @47
    @16
    @57
    vf
    @47
    @16
    @57
    @47
    @16
    wa
    #
    @52
    @56
    @58
    @20
    cvv
    @51
    wf
    #
    @52
    @58
    @13
    cvv
    @0
    wf
    #
    @18
    cvv
    wcel
    #
    @35
    @1
    cvv
    wcel
    #
    @59
    @14
    @60
    @47
    @15
    @14
    @60
    @13
    @0
    dffn2
    #
    biimpi
    ad2antrl
    @61
    @58
    vz
    vex
    #
    a1i
    @34
    @35
    @38
    @16
    simpllr
    #
    @62
    @58
    vw
    vex
    #
    a1i
    @13
    cvv
    @0
    cvv
    @18
    @1
    fsnunf
    #
    syl121anc
    @20
    @51
    dffn2
    #
    sylibr
    @58
    @38
    @35
    @15
    @56
    @36
    @38
    @16
    simplr
    @65
    @47
    @14
    @15
    simprr
    @38
    @35
    wa
    #
    @15
    wa
    #
    @55
    vx
    @20
    @69
    @15
    vx
    @69
    vx
    nfv
    @7
    vx
    @13
    nfra1
    #
    nfan
    @70
    @3
    @20
    wcel
    #
    @55
    @70
    @72
    wa
    #
    @4
    @54
    @73
    @4
    wa
    #
    @3
    @13
    wcel
    #
    @54
    @3
    @19
    wcel
    #
    @74
    @75
    wa
    #
    @53
    @5
    @3
    @77
    @18
    @3
    wne
    #
    @53
    @5
    wceq
    #
    @77
    @75
    @35
    wa
    #
    @78
    @77
    @75
    @35
    @74
    @75
    simpr
    #
    @74
    @35
    @75
    @73
    @35
    @4
    @38
    @35
    @15
    @72
    simpllr
    adantr
    adantr
    jca
    @80
    @3
    @18
    @3
    @18
    @13
    nelne2
    necomd
    #
    syl
    @0
    @18
    @1
    @3
    fvunsn
    #
    syl
    @77
    @75
    @15
    @4
    @6
    @81
    @74
    @15
    @75
    @69
    @15
    @72
    @4
    simpllr
    adantr
    @73
    @4
    @75
    simplr
    @15
    vu
    cv
    #
    c0
    wne
    #
    @84
    @0
    cfv
    #
    @84
    wcel
    #
    wi
    #
    vu
    @13
    wral
    @75
    @7
    @88
    @7
    vu
    vx
    @13
    @84
    @3
    wceq
    #
    @85
    @4
    @87
    @6
    @84
    @3
    c0
    neeq1
    @89
    @87
    @5
    @84
    wcel
    @6
    @89
    @86
    @5
    @84
    @84
    @3
    @0
    fveq2
    eleq1d
    @84
    @3
    @5
    eleq2
    bitrd
    imbi12d
    #
    cbvralv
    @88
    @7
    vu
    @3
    @13
    @90
    rspcv
    syl5bir
    #
    syl3c
    eqeltrd
    @74
    @76
    wa
    @38
    @76
    @4
    @54
    @74
    @38
    @76
    @38
    @35
    @15
    @72
    @4
    simp-4l
    adantr
    @74
    @76
    simpr
    @73
    @4
    @76
    simplr
    @38
    @76
    @4
    w3a
    #
    @54
    @3
    c0
    @92
    @3
    @18
    c0
    @76
    @38
    @3
    @18
    wceq
    #
    @4
    @3
    @18
    elsni
    #
    3ad2ant2
    @38
    @76
    @4
    simp1
    eqtrd
    @38
    @76
    @4
    simp3
    pm2.21ddne
    syl3anc
    @74
    @72
    @75
    @76
    wo
    #
    @70
    @72
    @4
    simplr
    @3
    @13
    @19
    elun
    #
    sylib
    mpjaodan
    ex
    ex
    ralrimi
    syl21anc
    jca
    ex
    eximdv
    @57
    @46
    vf
    @45
    @57
    vg
    @51
    @0
    @50
    vf
    vex
    @49
    snex
    unex
    @39
    @51
    wceq
    #
    @40
    @52
    @44
    @56
    @20
    @39
    @51
    fneq1
    @97
    @43
    @55
    vx
    @20
    @97
    @42
    @54
    @4
    @97
    @41
    @53
    @3
    @3
    @39
    @51
    fveq1
    eleq1d
    imbi2d
    ralbidv
    anbi12d
    spcev
    #
    eximi
    syl6
    @46
    vf
    ax5e
    #
    syl6
    imp
    an32s
    @23
    @45
    vf
    vg
    @0
    @39
    wceq
    #
    @21
    @40
    @22
    @44
    @20
    @0
    @39
    fneq1
    @100
    @7
    @43
    vx
    @20
    @100
    @6
    @42
    @4
    @100
    @5
    @41
    @3
    @3
    @0
    @39
    fveq1
    eleq1d
    imbi2d
    ralbidv
    anbi12d
    cbvexv
    #
    sylibr
    @37
    @38
    wn
    #
    wa
    #
    @35
    @1
    @18
    wcel
    #
    vw
    wex
    #
    @17
    wa
    #
    wa
    #
    @24
    @103
    @35
    @106
    @34
    @35
    @17
    @102
    simpllr
    @103
    @105
    @17
    @103
    @102
    @105
    @37
    @102
    simpr
    vw
    @18
    neq0
    sylib
    @36
    @17
    @102
    simplr
    jca
    jca
    @107
    @46
    @24
    @107
    @48
    vw
    wex
    #
    @46
    @35
    @106
    @108
    @106
    @104
    @16
    wa
    #
    vf
    wex
    vw
    wex
    @35
    @108
    @104
    @16
    vw
    vf
    eeanv
    @35
    @109
    @46
    vw
    vf
    @35
    @109
    @46
    @35
    @109
    wa
    #
    @57
    @46
    @110
    @52
    @56
    @110
    @59
    @52
    @110
    @60
    @61
    @35
    @62
    @59
    @110
    @14
    @60
    @35
    @104
    @14
    @15
    simprrl
    #
    @63
    sylib
    @61
    @110
    @64
    a1i
    @35
    @109
    simpl
    @62
    @110
    @66
    a1i
    @67
    syl121anc
    @68
    sylibr
    @110
    @55
    vx
    @20
    @35
    @109
    vx
    @35
    vx
    nfv
    @104
    @16
    vx
    @104
    vx
    nfv
    @14
    @15
    vx
    @14
    vx
    nfv
    @71
    nfan
    nfan
    nfan
    @110
    @72
    @55
    @110
    @72
    wa
    #
    @4
    @54
    @112
    @4
    wa
    #
    @75
    @54
    @76
    @113
    @75
    wa
    #
    @53
    @5
    @3
    @114
    @80
    @79
    @114
    @75
    @35
    @113
    @75
    simpr
    #
    @35
    @109
    @72
    @4
    @75
    simp-4l
    jca
    @80
    @78
    @79
    @82
    @83
    syl
    syl
    @114
    @75
    @15
    @4
    @6
    @115
    @113
    @15
    @75
    @112
    @15
    @4
    @110
    @15
    @72
    @35
    @104
    @14
    @15
    simprrr
    adantr
    adantr
    adantr
    @112
    @4
    @75
    simplr
    @91
    syl3c
    eqeltrd
    @113
    @76
    wa
    #
    @1
    @18
    @53
    @3
    @113
    @104
    @76
    @112
    @104
    @4
    @35
    @104
    @16
    @72
    simplrl
    adantr
    adantr
    @116
    @53
    @18
    @51
    cfv
    #
    @1
    @116
    @93
    @53
    @117
    wceq
    @116
    @76
    @93
    @113
    @76
    simpr
    @94
    syl
    #
    @3
    @18
    @51
    fveq2
    syl
    @116
    @61
    @62
    @18
    @0
    cdm
    #
    wcel
    wn
    @117
    @1
    wceq
    @61
    @116
    @64
    a1i
    @62
    @116
    @66
    a1i
    @116
    @119
    @13
    @18
    @35
    @109
    @72
    @4
    @76
    simp-4l
    @116
    @14
    @119
    @13
    wceq
    @113
    @14
    @76
    @112
    @14
    @4
    @110
    @14
    @72
    @111
    adantr
    adantr
    adantr
    @13
    @0
    fndm
    syl
    neleqtrrd
    @0
    cvv
    cvv
    @18
    @1
    fsnunfv
    syl3anc
    eqtrd
    @118
    3eltr4d
    @113
    @72
    @95
    @110
    @72
    @4
    simplr
    @96
    sylib
    mpjaodan
    ex
    ex
    ralrimi
    jca
    @98
    syl
    ex
    2eximdv
    syl5bir
    imp
    @48
    @46
    vw
    @99
    exlimiv
    syl
    @101
    sylibr
    syl
    pm2.61dan
    ex
    findcard2s
end
