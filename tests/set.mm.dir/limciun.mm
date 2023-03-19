include "climc.mm"
include "co.mm"
include "cc.mm"
include "cres.mm"
include "ciin.mm"
include "cin.mm"
include "wss.mm"
include "limccl.mm"
include "wral.mm"
include "limcresi.mm"
include "rgenw.mm"
include "ssiin.mm"
include "mpbir.mm"
include "ssini.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elriin.mm"
include "ciun.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "wrex.mm"
include "wi.mm"
include "simprl.mm"
include "wf.mm"
include "cfn.mm"
include "wex.mm"
include "ad2antrr.mm"
include "csb.mm"
include "simplrr.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfres.mm"
include "nfov.mm"
include "nfcri.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "reseq2d.mm"
include "oveq1d.mm"
include "eleq2d.mm"
include "rspc.mm"
include "mpan9.mm"
include "wb.mm"
include "ssiun2.mm"
include "cbviun.mm"
include "syl6sseqr.mm"
include "adantl.mm"
include "fssresd.mm"
include "simpr.mm"
include "nfss.mm"
include "sseq1d.mm"
include "sylc.mm"
include "eqid.mm"
include "ellimc2.mm"
include "adantlr.mm"
include "mpbid.mm"
include "simprd.mm"
include "simplrl.mm"
include "rsp.mm"
include "syl3c.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nfdif.mm"
include "nfin.mm"
include "nfima.mm"
include "nfan.mm"
include "nfrex.mm"
include "difeq1d.mm"
include "ineq2d.mm"
include "imaeq12d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvral.mm"
include "sylibr.mm"
include "eleq2.mm"
include "ineq1.mm"
include "imaeq2d.mm"
include "anbi12d.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "crn.mm"
include "cint.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "frn.mm"
include "ad2antrl.mm"
include "wfo.mm"
include "adantr.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "rintopn.mm"
include "syl3anc.mm"
include "simpl.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "ralrn.mm"
include "syl.mm"
include "mpbird.mm"
include "elrint.mm"
include "sylanbrc.mm"
include "indifcom.mm"
include "iunin1.mm"
include "eqtr4i.mm"
include "imaeq2i.mm"
include "imaiun.mm"
include "eqtri.mm"
include "inss2.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "intss1.mm"
include "syl5ss.mm"
include "ssdifd.mm"
include "sslin.mm"
include "imass2.mm"
include "3syl.mm"
include "inss1.mm"
include "resima2.mm"
include "ax-mp.mm"
include "sstr2.mm"
include "adantld.mm"
include "ralimdva.mm"
include "imp.mm"
include "iunss.mm"
include "syl5eqss.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "exlimddv.mm"
include "expr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem limciun
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let va: setvar a
  let vg: setvar g
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  assume limciun.1: |- ( ph -> A e. Fin )
  assume limciun.2: |- ( ph -> A. x e. A B C_ CC )
  assume limciun.3: |- ( ph -> F : U_ x e. A B --> CC )
  assume limciun.4: |- ( ph -> C e. CC )

  disjoint A x
  disjoint C x
  disjoint F x
  disjoint a g
  disjoint a k
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint g k
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C a
  disjoint C g
  disjoint C k
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint F a
  disjoint F g
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint B a
  disjoint B g
  disjoint B k
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint a ph
  disjoint g ph
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint ph y
  assert |- ( ph -> ( F limCC C ) = ( CC i^i |^|_ x e. A ( ( F |` B ) limCC C ) ) )

  proof
    wph
    cF
    cC
    climc
    co
    #
    cc
    vx
    cA
    cF
    cB
    cres
    #
    cC
    climc
    co
    #
    ciin
    #
    cin
    #
    @0
    @4
    wss
    wph
    @0
    cc
    @3
    cC
    cF
    limccl
    @0
    @3
    wss
    @0
    @2
    wss
    #
    vx
    cA
    wral
    @5
    vx
    cA
    cC
    cB
    cF
    limcresi
    rgenw
    vx
    cA
    @2
    @0
    ssiin
    mpbir
    ssini
    a1i
    wph
    vy
    @4
    @0
    vy
    cv
    #
    @4
    wcel
    @6
    cc
    wcel
    #
    @6
    @2
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    wph
    @6
    @0
    wcel
    #
    vx
    cc
    @6
    @2
    cA
    elriin
    wph
    @10
    @11
    wph
    @10
    wa
    #
    @11
    @7
    @6
    vu
    cv
    #
    wcel
    #
    cC
    vv
    cv
    #
    wcel
    #
    cF
    @15
    vx
    cA
    cB
    ciun
    #
    cC
    csn
    #
    cdif
    #
    cin
    #
    cima
    #
    @13
    wss
    #
    wa
    #
    vv
    ccnfld
    ctopn
    cfv
    #
    wrex
    #
    wi
    #
    vu
    @24
    wral
    wph
    @7
    @9
    simprl
    @12
    @26
    vu
    @24
    @12
    @13
    @24
    wcel
    #
    @14
    @25
    @12
    @27
    @14
    wa
    #
    wa
    #
    cA
    @24
    vg
    cv
    #
    wf
    #
    cC
    vx
    cv
    #
    @30
    cfv
    #
    wcel
    #
    @1
    @33
    cB
    @18
    cdif
    #
    cin
    #
    cima
    #
    @13
    wss
    #
    wa
    #
    vx
    cA
    wral
    #
    wa
    #
    @25
    vg
    @29
    cA
    cfn
    wcel
    #
    cC
    vk
    cv
    #
    wcel
    #
    @1
    @43
    @35
    cin
    #
    cima
    #
    @13
    wss
    #
    wa
    #
    vk
    @24
    wrex
    #
    vx
    cA
    wral
    #
    @41
    vg
    wex
    wph
    @42
    @10
    @28
    limciun.1
    ad2antrr
    #
    @29
    @44
    cF
    vx
    va
    cv
    #
    cB
    csb
    #
    cres
    #
    @43
    @53
    @18
    cdif
    #
    cin
    #
    cima
    #
    @13
    wss
    #
    wa
    #
    vk
    @24
    wrex
    #
    va
    cA
    wral
    @50
    @29
    @60
    va
    cA
    @29
    @52
    cA
    wcel
    #
    wa
    #
    @14
    @60
    wi
    #
    vu
    @24
    wral
    #
    @27
    @14
    @60
    @62
    @7
    @64
    @62
    @6
    @54
    cC
    climc
    co
    #
    wcel
    #
    @7
    @64
    wa
    #
    @29
    @9
    @61
    @66
    wph
    @7
    @9
    @28
    simplrr
    @8
    @66
    vx
    @52
    cA
    vx
    vy
    @65
    vx
    @54
    cC
    climc
    vx
    cF
    @53
    vx
    cF
    nfcv
    vx
    @52
    cB
    nfcsb1v
    #
    nfres
    #
    vx
    climc
    nfcv
    vx
    cC
    nfcv
    nfov
    nfcri
    @32
    @52
    wceq
    #
    @2
    @65
    @6
    @70
    @1
    @54
    cC
    climc
    @70
    cB
    @53
    cF
    vx
    @52
    cB
    csbeq1a
    #
    reseq2d
    #
    oveq1d
    eleq2d
    rspc
    mpan9
    @12
    @61
    @66
    @67
    wb
    @28
    @12
    @61
    wa
    #
    vk
    vu
    @53
    cC
    @6
    @54
    @24
    @73
    @17
    cc
    @53
    cF
    wph
    @17
    cc
    cF
    wf
    #
    @10
    @61
    limciun.3
    ad2antrr
    @61
    @53
    @17
    wss
    @12
    @61
    @53
    va
    cA
    @53
    ciun
    @17
    va
    cA
    @53
    ssiun2
    vx
    va
    cA
    cB
    @53
    va
    cB
    nfcv
    @68
    @71
    cbviun
    syl6sseqr
    adantl
    fssresd
    @73
    @61
    cB
    cc
    wss
    #
    vx
    cA
    wral
    #
    @53
    cc
    wss
    #
    @12
    @61
    simpr
    wph
    @76
    @10
    @61
    limciun.2
    ad2antrr
    @75
    @77
    vx
    @52
    cA
    vx
    @53
    cc
    @68
    vx
    cc
    nfcv
    nfss
    @70
    cB
    @53
    cc
    @71
    sseq1d
    rspc
    sylc
    wph
    cC
    cc
    wcel
    #
    @10
    @61
    limciun.4
    ad2antrr
    @24
    eqid
    #
    ellimc2
    adantlr
    mpbid
    simprd
    @12
    @27
    @14
    @61
    simplrl
    @12
    @27
    @14
    @61
    simplrr
    @63
    vu
    @24
    rsp
    syl3c
    ralrimiva
    @49
    @60
    vx
    va
    cA
    @49
    va
    nfv
    @59
    vx
    vk
    @24
    vx
    @24
    nfcv
    @44
    @58
    vx
    @44
    vx
    nfv
    vx
    @57
    @13
    vx
    @54
    @56
    @69
    vx
    @43
    @55
    vx
    @43
    nfcv
    vx
    @53
    @18
    @68
    vx
    @18
    nfcv
    nfdif
    nfin
    nfima
    vx
    @13
    nfcv
    nfss
    nfan
    nfrex
    @70
    @48
    @59
    vk
    @24
    @70
    @47
    @58
    @44
    @70
    @46
    @57
    @13
    @70
    @1
    @54
    @45
    @56
    @72
    @70
    @35
    @55
    @43
    @70
    cB
    @53
    @18
    @71
    difeq1d
    ineq2d
    imaeq12d
    sseq1d
    anbi2d
    rexbidv
    cbvral
    sylibr
    @48
    @39
    vx
    vk
    cA
    @24
    vg
    @43
    @33
    wceq
    #
    @44
    @34
    @47
    @38
    @43
    @33
    cC
    eleq2
    @80
    @46
    @37
    @13
    @80
    @45
    @36
    @1
    @43
    @33
    @35
    ineq1
    imaeq2d
    sseq1d
    anbi12d
    ac6sfi
    syl2anc
    @29
    @41
    wa
    #
    cc
    @30
    crn
    #
    cint
    #
    cin
    #
    @24
    wcel
    #
    cC
    @84
    wcel
    #
    cF
    @84
    @19
    cin
    #
    cima
    #
    @13
    wss
    #
    @25
    @81
    @24
    ctop
    wcel
    #
    @82
    @24
    wss
    #
    @82
    cfn
    wcel
    #
    @85
    @90
    @81
    @24
    @79
    cnfldtop
    a1i
    @31
    @91
    @29
    @40
    cA
    @24
    @30
    frn
    ad2antrl
    @81
    @42
    cA
    @82
    @30
    wfo
    #
    @92
    @29
    @42
    @41
    @51
    adantr
    @81
    @30
    cA
    wfn
    #
    @93
    @31
    @94
    @29
    @40
    cA
    @24
    @30
    ffn
    #
    ad2antrl
    #
    cA
    @30
    dffn4
    sylib
    cA
    @82
    @30
    fofi
    syl2anc
    @82
    @24
    cc
    cc
    @24
    @24
    @79
    cnfldtopon
    toponunii
    rintopn
    syl3anc
    @81
    @78
    cC
    vz
    cv
    #
    wcel
    #
    vz
    @82
    wral
    #
    @86
    @12
    @78
    @28
    @41
    wph
    @78
    @10
    limciun.4
    adantr
    #
    ad2antrr
    @81
    @99
    @34
    vx
    cA
    wral
    #
    @40
    @101
    @29
    @31
    @39
    @34
    vx
    cA
    @34
    @38
    simpl
    ralimi
    ad2antll
    @81
    @94
    @99
    @101
    wb
    @96
    @98
    @34
    vz
    vx
    cA
    @30
    @97
    @33
    cC
    eleq2
    ralrn
    syl
    mpbird
    vz
    cc
    @82
    cC
    elrint
    sylanbrc
    @81
    @88
    vx
    cA
    cF
    cB
    @84
    @18
    cdif
    #
    cin
    #
    cima
    #
    ciun
    #
    @13
    @88
    cF
    vx
    cA
    @103
    ciun
    #
    cima
    @105
    @87
    @106
    cF
    @87
    @17
    @102
    cin
    @106
    @84
    @17
    @18
    indifcom
    vx
    cA
    @102
    cB
    iunin1
    eqtr4i
    imaeq2i
    vx
    cF
    cA
    @103
    imaiun
    eqtri
    @81
    @104
    @13
    wss
    #
    vx
    cA
    wral
    #
    @105
    @13
    wss
    @41
    @108
    @29
    @31
    @40
    @108
    @31
    @39
    @107
    vx
    cA
    @31
    @32
    cA
    wcel
    #
    wa
    #
    @38
    @107
    @34
    @110
    @104
    @37
    wss
    @38
    @107
    wi
    @110
    @104
    cF
    cB
    @33
    @18
    cdif
    #
    cin
    #
    cima
    #
    @37
    @110
    @102
    @111
    wss
    @103
    @112
    wss
    @104
    @113
    wss
    @110
    @84
    @33
    @18
    @110
    @84
    @83
    @33
    cc
    @83
    inss2
    @110
    @33
    @82
    wcel
    #
    @83
    @33
    wss
    @31
    @94
    @109
    @114
    @95
    cA
    @32
    @30
    fnfvelrn
    sylan
    @33
    @82
    intss1
    syl
    syl5ss
    ssdifd
    @102
    @111
    cB
    sslin
    @103
    @112
    cF
    imass2
    3syl
    @37
    @1
    @112
    cima
    #
    @113
    @36
    @112
    @1
    @33
    cB
    @18
    indifcom
    imaeq2i
    @112
    cB
    wss
    @115
    @113
    wceq
    cB
    @111
    inss1
    cF
    @112
    cB
    resima2
    ax-mp
    eqtri
    syl6sseqr
    @104
    @37
    @13
    sstr2
    syl
    adantld
    ralimdva
    imp
    adantl
    vx
    cA
    @104
    @13
    iunss
    sylibr
    syl5eqss
    @23
    @86
    @89
    wa
    vv
    @84
    @24
    @15
    @84
    wceq
    #
    @16
    @86
    @22
    @89
    @15
    @84
    cC
    eleq2
    @116
    @21
    @88
    @13
    @116
    @20
    @87
    cF
    @15
    @84
    @19
    ineq1
    imaeq2d
    sseq1d
    anbi12d
    rspcev
    syl12anc
    exlimddv
    expr
    ralrimiva
    @12
    vv
    vu
    @17
    cC
    @6
    cF
    @24
    wph
    @74
    @10
    limciun.3
    adantr
    wph
    @17
    cc
    wss
    #
    @10
    wph
    @76
    @117
    limciun.2
    vx
    cA
    cB
    cc
    iunss
    sylibr
    adantr
    @100
    @79
    ellimc2
    mpbir2and
    ex
    syl5bi
    ssrdv
    eqssd
end
