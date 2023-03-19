include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cdvn.mm"
include "cfv.mm"
include "wceq.mm"
include "simpr.mm"
include "simpl.mm"
include "csb.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2.mm"
include "csbeq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "csbeq1a.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "cuz.mm"
include "cc.mm"
include "wss.mm"
include "cpm.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "syl.mm"
include "cvv.mm"
include "wf.mm"
include "cnex.mm"
include "a1i.mm"
include "adantr.mm"
include "wne.mm"
include "divcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "dvn0.mm"
include "syl2anc.mm"
include "id.mm"
include "cn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfmpt.mm"
include "nfeq.mm"
include "nfim.mm"
include "c0ex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "vtoclf.mm"
include "fveq1d.mm"
include "w3a.mm"
include "0re.mm"
include "nfel.mm"
include "3anbi3d.mm"
include "eleq1d.mm"
include "vtoclgf.mm"
include "ax-mp.mm"
include "syl3anc.mm"
include "fvmpt2.mm"
include "eqtr2d.mm"
include "3eqtrrd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cfzo.mm"
include "simp3.mm"
include "simp1.mm"
include "mpd.mm"
include "3adant1.mm"
include "cdv.mm"
include "ad2antrr.mm"
include "elfzofz.mm"
include "elfznn0.mm"
include "ad2antlr.mm"
include "sylanl2.mm"
include "dvnp1.mm"
include "oveq2.mm"
include "adantl.mm"
include "sylan2.mm"
include "simplr.mm"
include "3jca.mm"
include "nfcsb1.mm"
include "sylc.mm"
include "fzofzp1.mm"
include "chvar.mm"
include "oveq2d.mm"
include "jca.mm"
include "3eqtrd.mm"
include "dvmptdivc.mm"
include "syl21anc.mm"
include "3exp.mm"
include "fzind2.mm"

theorem dvnmptdivc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vn: setvar n
  let cM: class M
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  assume dvnmptdivc.s: |- ( ph -> S e. { RR , CC } )
  assume dvnmptdivc.x: |- ( ph -> X C_ S )
  assume dvnmptdivc.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvnmptdivc.b: |- ( ( ph /\ x e. X /\ n e. ( 0 ... M ) ) -> B e. CC )
  assume dvnmptdivc.dvn: |- ( ( ph /\ n e. ( 0 ... M ) ) -> ( ( S Dn ( x e. X |-> A ) ) ` n ) = ( x e. X |-> B ) )
  assume dvnmptdivc.c: |- ( ph -> C e. CC )
  assume dvnmptdivc.cne0: |- ( ph -> C =/= 0 )
  assume dvnmptdivc.8: |- ( ph -> M e. NN0 )

  disjoint A n
  disjoint C x
  disjoint M n
  disjoint M x
  disjoint n x
  disjoint S n
  disjoint S x
  disjoint X n
  disjoint X x
  disjoint n ph
  disjoint ph x
  disjoint A j
  disjoint A k
  disjoint j k
  disjoint j n
  disjoint k n
  disjoint B j
  disjoint B k
  disjoint C j
  disjoint C k
  disjoint j x
  disjoint k x
  disjoint M j
  disjoint M k
  disjoint S j
  disjoint S k
  disjoint X j
  disjoint X k
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ( ph /\ n e. ( 0 ... M ) ) -> ( ( S Dn ( x e. X |-> ( A / C ) ) ) ` n ) = ( x e. X |-> ( B / C ) ) )

  proof
    wph
    vn
    cv
    #
    cc0
    cM
    cfz
    co
    #
    wcel
    #
    wa
    #
    @2
    wph
    @0
    cS
    vx
    cX
    cA
    cC
    cdiv
    co
    #
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    vx
    cX
    cB
    cC
    cdiv
    co
    #
    cmpt
    #
    wceq
    #
    wph
    @2
    simpr
    wph
    @2
    simpl
    wph
    vk
    cv
    #
    @6
    cfv
    #
    vx
    cX
    vn
    @11
    cB
    csb
    #
    cC
    cdiv
    co
    #
    cmpt
    #
    wceq
    #
    wi
    wph
    cc0
    @6
    cfv
    #
    vx
    cX
    vn
    cc0
    cB
    csb
    #
    cC
    cdiv
    co
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wph
    vj
    cv
    #
    @6
    cfv
    #
    vx
    cX
    vn
    @23
    cB
    csb
    #
    cC
    cdiv
    co
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wph
    @23
    c1
    caddc
    co
    #
    @6
    cfv
    #
    vx
    cX
    vn
    @30
    cB
    csb
    #
    cC
    cdiv
    co
    #
    cmpt
    #
    wceq
    #
    wi
    wph
    @10
    wi
    vk
    vj
    @0
    cc0
    cM
    @11
    cc0
    wceq
    #
    @16
    @21
    wph
    @36
    @12
    @17
    @15
    @20
    @11
    cc0
    @6
    fveq2
    @36
    vx
    cX
    @14
    @19
    @36
    @13
    @18
    cC
    cdiv
    vn
    @11
    cc0
    cB
    csbeq1
    oveq1d
    mpteq2dv
    eqeq12d
    imbi2d
    @11
    @23
    wceq
    #
    @16
    @28
    wph
    @37
    @12
    @24
    @15
    @27
    @11
    @23
    @6
    fveq2
    @37
    vx
    cX
    @14
    @26
    @37
    @13
    @25
    cC
    cdiv
    vn
    @11
    @23
    cB
    csbeq1
    oveq1d
    mpteq2dv
    eqeq12d
    imbi2d
    @11
    @30
    wceq
    #
    @16
    @35
    wph
    @38
    @12
    @31
    @15
    @34
    @11
    @30
    @6
    fveq2
    @38
    vx
    cX
    @14
    @33
    @38
    @13
    @32
    cC
    cdiv
    vn
    @11
    @30
    cB
    csbeq1
    oveq1d
    mpteq2dv
    eqeq12d
    imbi2d
    @11
    @0
    wceq
    #
    @16
    @10
    wph
    @39
    @12
    @7
    @15
    @9
    @11
    @0
    @6
    fveq2
    @39
    vx
    cX
    @14
    @8
    @39
    @13
    cB
    cC
    cdiv
    @39
    cB
    @13
    cB
    @13
    wceq
    vn
    vk
    vn
    @11
    cB
    csbeq1a
    equcoms
    eqcomd
    oveq1d
    mpteq2dv
    eqeq12d
    imbi2d
    @22
    cM
    cc0
    cuz
    cfv
    #
    wcel
    #
    wph
    @17
    @5
    @20
    wph
    cS
    cc
    wss
    #
    @5
    cc
    cS
    cpm
    co
    #
    wcel
    #
    @17
    @5
    wceq
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    @42
    dvnmptdivc.s
    cS
    recnprss
    syl
    #
    wph
    cc
    cvv
    wcel
    #
    @46
    cX
    cc
    @5
    wf
    cX
    cS
    wss
    #
    @44
    @48
    wph
    cnex
    a1i
    #
    dvnmptdivc.s
    wph
    vx
    cX
    @4
    cc
    @5
    wph
    vx
    cv
    #
    cX
    wcel
    #
    wa
    #
    cA
    cC
    dvnmptdivc.a
    wph
    cC
    cc
    wcel
    #
    @52
    dvnmptdivc.c
    adantr
    wph
    cC
    cc0
    wne
    #
    @52
    dvnmptdivc.cne0
    adantr
    divcld
    @5
    eqid
    fmptd
    dvnmptdivc.x
    cc
    cS
    cX
    @5
    cvv
    @45
    elpm2r
    syl22anc
    #
    cS
    @5
    dvn0
    syl2anc
    wph
    vx
    cX
    @4
    @19
    @53
    cA
    @18
    cC
    cdiv
    @53
    @18
    @51
    cc0
    cS
    vx
    cX
    cA
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    @51
    @57
    cfv
    #
    cA
    @53
    @60
    @51
    vx
    cX
    @18
    cmpt
    #
    cfv
    #
    @18
    wph
    @60
    @63
    wceq
    @52
    wph
    @51
    @59
    @62
    wph
    wph
    cc0
    @1
    wcel
    #
    @59
    @62
    wceq
    #
    wph
    id
    #
    wph
    @41
    @64
    wph
    cM
    cn0
    @40
    dvnmptdivc.8
    nn0uz
    syl6eleq
    cc0
    cM
    eluzfz1
    syl
    #
    @3
    @0
    @58
    cfv
    #
    vx
    cX
    cB
    cmpt
    #
    wceq
    #
    wi
    #
    wph
    @64
    wa
    #
    @65
    wi
    vn
    cc0
    @72
    @65
    vn
    @72
    vn
    nfv
    vn
    @59
    @62
    vn
    @59
    nfcv
    vn
    vx
    cX
    @18
    vn
    cX
    nfcv
    #
    vn
    cc0
    cB
    nfcsb1v
    #
    nfmpt
    nfeq
    nfim
    c0ex
    @0
    cc0
    wceq
    #
    @3
    @72
    @70
    @65
    @75
    @2
    @64
    wph
    @0
    cc0
    @1
    eleq1
    #
    anbi2d
    @75
    @68
    @59
    @69
    @62
    @0
    cc0
    @58
    fveq2
    @75
    vx
    cX
    cB
    @18
    vn
    cc0
    cB
    csbeq1a
    #
    mpteq2dv
    eqeq12d
    imbi12d
    dvnmptdivc.dvn
    vtoclf
    syl2anc
    fveq1d
    adantr
    @53
    @52
    @18
    cc
    wcel
    #
    @63
    @18
    wceq
    wph
    @52
    simpr
    #
    @53
    wph
    @52
    @64
    @78
    wph
    @52
    simpl
    @79
    wph
    @64
    @52
    @67
    adantr
    cc0
    cr
    wcel
    wph
    @52
    @64
    w3a
    #
    @78
    wi
    #
    0re
    wph
    @52
    @2
    w3a
    #
    cB
    cc
    wcel
    #
    wi
    #
    @81
    vn
    cc0
    cr
    vn
    cc0
    nfcv
    @80
    @78
    vn
    @80
    vn
    nfv
    vn
    @18
    cc
    @74
    vn
    cc
    nfcv
    #
    nfel
    nfim
    @75
    @82
    @80
    @83
    @78
    @75
    @2
    @64
    wph
    @52
    @76
    3anbi3d
    @75
    cB
    @18
    cc
    @77
    eleq1d
    imbi12d
    dvnmptdivc.b
    vtoclgf
    ax-mp
    syl3anc
    vx
    cX
    @18
    cc
    @62
    @62
    eqid
    fvmpt2
    syl2anc
    eqtr2d
    wph
    @60
    @61
    wceq
    @52
    wph
    @51
    @59
    @57
    wph
    @42
    @57
    @43
    wcel
    #
    @59
    @57
    wceq
    @47
    wph
    @48
    @46
    cX
    cc
    @57
    wf
    @49
    @86
    @50
    dvnmptdivc.s
    wph
    vx
    cX
    cA
    cc
    @57
    dvnmptdivc.a
    @57
    eqid
    #
    fmptd
    dvnmptdivc.x
    cc
    cS
    cX
    @57
    cvv
    @45
    elpm2r
    syl22anc
    #
    cS
    @57
    dvn0
    syl2anc
    fveq1d
    adantr
    @53
    @52
    cA
    cc
    wcel
    @61
    cA
    wceq
    @79
    dvnmptdivc.a
    vx
    cX
    cA
    cc
    @57
    @87
    fvmpt2
    syl2anc
    3eqtrrd
    oveq1d
    mpteq2dva
    eqtrd
    a1i
    @23
    cc0
    cM
    cfzo
    co
    wcel
    #
    @29
    wph
    @35
    @89
    @29
    wph
    w3a
    wph
    @89
    @28
    @35
    @89
    @29
    wph
    simp3
    @89
    @29
    wph
    simp1
    @29
    wph
    @28
    @89
    @29
    wph
    wa
    wph
    @28
    @29
    wph
    simpr
    @29
    wph
    simpl
    mpd
    3adant1
    wph
    @89
    wa
    #
    @28
    wa
    #
    @31
    cS
    @24
    cdv
    co
    #
    cS
    @27
    cdv
    co
    #
    @34
    @91
    @42
    @44
    @23
    cn0
    wcel
    #
    @31
    @92
    wceq
    #
    wph
    @42
    @89
    @28
    @47
    ad2antrr
    wph
    @44
    @89
    @28
    @56
    ad2antrr
    @89
    wph
    @23
    @1
    wcel
    #
    @28
    @94
    @23
    cc0
    cM
    elfzofz
    #
    @96
    @94
    wph
    @28
    @23
    cM
    elfznn0
    #
    ad2antlr
    sylanl2
    cS
    @5
    @23
    dvnp1
    #
    syl3anc
    #
    @28
    @92
    @93
    wceq
    @90
    @24
    @27
    cS
    cdv
    oveq2
    adantl
    #
    @91
    @34
    @31
    @92
    @93
    @91
    @31
    @34
    @91
    @31
    @92
    @93
    @34
    @90
    @95
    @28
    @90
    @42
    @44
    @94
    @95
    wph
    @42
    @89
    @47
    adantr
    #
    wph
    @44
    @89
    @56
    adantr
    @89
    wph
    @96
    @94
    @97
    wph
    @96
    wa
    #
    @96
    @94
    wph
    @96
    simpr
    @98
    syl
    sylan2
    #
    @99
    syl3anc
    adantr
    @101
    @90
    @93
    @34
    wceq
    @28
    @90
    vx
    @25
    @32
    cC
    cS
    cc
    cX
    wph
    @46
    @89
    dvnmptdivc.s
    adantr
    @89
    wph
    @96
    @52
    @25
    cc
    wcel
    #
    @97
    @103
    @52
    wa
    #
    @96
    wph
    @52
    @96
    w3a
    #
    @105
    wph
    @96
    @52
    simplr
    #
    @106
    wph
    @52
    @96
    wph
    wph
    @96
    @52
    @66
    ad2antrr
    #
    @103
    @52
    simpr
    @108
    3jca
    @84
    @107
    @105
    wi
    vn
    @23
    @1
    vn
    @23
    nfcv
    #
    @107
    @105
    vn
    @107
    vn
    nfv
    vn
    @25
    cc
    vn
    @23
    cB
    @110
    nfcsb1
    #
    @85
    nfel
    nfim
    @0
    @23
    wceq
    #
    @82
    @107
    @83
    @105
    @112
    @2
    @96
    wph
    @52
    @0
    @23
    @1
    eleq1
    #
    3anbi3d
    @112
    cB
    @25
    cc
    vn
    @23
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    dvnmptdivc.b
    vtoclgf
    sylc
    sylanl2
    @90
    @52
    wa
    #
    @30
    @1
    wcel
    #
    wph
    @52
    @116
    w3a
    #
    @32
    cc
    wcel
    #
    @89
    @116
    wph
    @52
    cc0
    cM
    @23
    fzofzp1
    #
    ad2antlr
    #
    @115
    wph
    @52
    @116
    @89
    wph
    @96
    @52
    wph
    @97
    @109
    sylanl2
    @90
    @52
    simpr
    @120
    3jca
    @84
    @117
    @118
    wi
    vn
    @30
    @1
    vn
    @30
    nfcv
    #
    @117
    @118
    vn
    @117
    vn
    nfv
    vn
    @32
    cc
    vn
    @30
    cB
    @121
    nfcsb1
    #
    @85
    nfel
    nfim
    @0
    @30
    wceq
    #
    @82
    @117
    @83
    @118
    @123
    @2
    @116
    wph
    @52
    @0
    @30
    @1
    eleq1
    #
    3anbi3d
    @123
    cB
    @32
    cc
    vn
    @30
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    dvnmptdivc.b
    vtoclgf
    sylc
    @90
    cS
    vx
    cX
    @25
    cmpt
    #
    cdv
    co
    cS
    @23
    @58
    cfv
    #
    cdv
    co
    #
    @30
    @58
    cfv
    #
    vx
    cX
    @32
    cmpt
    #
    @90
    @126
    @127
    cS
    cdv
    @90
    @127
    @126
    @90
    wph
    @96
    @127
    @126
    wceq
    #
    wph
    @89
    simpl
    #
    @89
    @96
    wph
    @97
    adantl
    @71
    @103
    @131
    wi
    vn
    vj
    @103
    @131
    vn
    @103
    vn
    nfv
    vn
    @127
    @126
    vn
    @127
    nfcv
    vn
    vx
    cX
    @25
    @73
    @111
    nfmpt
    nfeq
    nfim
    @112
    @3
    @103
    @70
    @131
    @112
    @2
    @96
    wph
    @113
    anbi2d
    @112
    @68
    @127
    @69
    @126
    @0
    @23
    @58
    fveq2
    @112
    vx
    cX
    cB
    @25
    @114
    mpteq2dv
    eqeq12d
    imbi12d
    dvnmptdivc.dvn
    chvar
    syl2anc
    eqcomd
    oveq2d
    @90
    @129
    @128
    @90
    @42
    @86
    @94
    @129
    @128
    wceq
    @102
    @90
    wph
    @86
    @132
    @88
    syl
    @104
    cS
    @57
    @23
    dvnp1
    syl3anc
    eqcomd
    @90
    @116
    wph
    @116
    wa
    #
    @129
    @130
    wceq
    #
    @89
    @116
    wph
    @119
    adantl
    #
    @90
    wph
    @116
    @132
    @135
    jca
    @71
    @133
    @134
    wi
    vn
    @30
    @1
    @121
    @133
    @134
    vn
    @133
    vn
    nfv
    vn
    @129
    @130
    vn
    @129
    nfcv
    vn
    vx
    cX
    @32
    @73
    @122
    nfmpt
    nfeq
    nfim
    @123
    @3
    @133
    @70
    @134
    @123
    @2
    @116
    wph
    @124
    anbi2d
    @123
    @68
    @129
    @69
    @130
    @0
    @30
    @58
    fveq2
    @123
    vx
    cX
    cB
    @32
    @125
    mpteq2dv
    eqeq12d
    imbi12d
    dvnmptdivc.dvn
    vtoclgf
    sylc
    3eqtrd
    wph
    @54
    @89
    dvnmptdivc.c
    adantr
    wph
    @55
    @89
    dvnmptdivc.cne0
    adantr
    dvmptdivc
    adantr
    3eqtrd
    eqcomd
    @100
    @101
    3eqtrrd
    3eqtrd
    syl21anc
    3exp
    fzind2
    sylc
end
