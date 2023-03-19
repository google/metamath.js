include "cv.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "iuneq1.mm"
include "mpteq1d.mm"
include "fveq2d.mm"
include "mpteq1.mm"
include "eqeq12d.mm"
include "0iun.mm"
include "ax-mp.mm"
include "mpt0.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "wss.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "csu.mm"
include "caddc.mm"
include "co.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfmpt.mm"
include "nffv.mm"
include "cfn.mm"
include "simprl.mm"
include "adantr.mm"
include "simpr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "syldan.mm"
include "simprr.mm"
include "cin.mm"
include "wn.mm"
include "eldifn.mm"
include "disjsn.mm"
include "sylibr.mm"
include "adantl.mm"
include "sylib.mm"
include "cc.mm"
include "cr.mm"
include "simpll.mm"
include "ssel2.mm"
include "adantll.mm"
include "recnd.mm"
include "adantlrr.mm"
include "csb.mm"
include "csbeq1a.mm"
include "nfcsb1v.mm"
include "vex.mm"
include "iunxsnf.mm"
include "syl6eqr.mm"
include "mpteq1i.mm"
include "eldifi.mm"
include "wi.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "sylan2.mm"
include "eqeltrd.mm"
include "adantrl.mm"
include "fsumsplitsn.mm"
include "eqcomd.mm"
include "cxad.mm"
include "iunxun.mm"
include "cvv.mm"
include "wral.mm"
include "ralrimiva.mm"
include "iunexg.mm"
include "iunss1.mm"
include "ssexd.mm"
include "adantrr.mm"
include "snssi.mm"
include "syl.mm"
include "wdisj.mm"
include "ad2antll.mm"
include "disjiun.mm"
include "syl13anc.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wrex.mm"
include "eliun.mm"
include "biimpi.mm"
include "w3a.mm"
include "simp1l.mm"
include "3adant3.mm"
include "simp3.mm"
include "syl3anc.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "sselda.mm"
include "adantlrl.mm"
include "sge0splitmpt.mm"
include "eqtrd.mm"
include "id.mm"
include "cico.mm"
include "cle.mm"
include "wbr.mm"
include "3expa.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0ge0.mm"
include "jca.mm"
include "elrege0.mm"
include "sge0fsum.mm"
include "fveq2.mm"
include "nfmpt1.mm"
include "cbvsum.mm"
include "fvexd.mm"
include "fvmpt2.mm"
include "sumeq2d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "fsumrecl.mm"
include "rexadd.mm"
include "snfi.mm"
include "unfi.mm"
include "ad4ant14.mm"
include "elunnel1.mm"
include "elsni.mm"
include "adantlll.mm"
include "pm2.61dan.mm"
include "sge0fsummpt.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "findcard2d.mm"

theorem sge0iunmptlemfi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume sge0iunmptlemfi.a: |- ( ph -> A e. Fin )
  assume sge0iunmptlemfi.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume sge0iunmptlemfi.dj: |- ( ph -> Disj_ x e. A B )
  assume sge0iunmptlemfi.c: |- ( ( ph /\ x e. A /\ k e. B ) -> C e. ( 0 [,] +oo ) )
  assume sge0iunmptlemfi.re: |- ( ( ph /\ x e. A ) -> ( sum^ ` ( k e. B |-> C ) ) e. RR )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B k
  disjoint C x
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( sum^ ` ( k e. U_ x e. A B |-> C ) ) = ( sum^ ` ( x e. A |-> ( sum^ ` ( k e. B |-> C ) ) ) ) )

  proof
    wph
    vk
    vx
    vy
    cv
    #
    cB
    ciun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vx
    @0
    vk
    cB
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    vk
    vx
    c0
    cB
    ciun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vx
    c0
    @5
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    vk
    vx
    vz
    cv
    #
    cB
    ciun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vx
    @14
    @5
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    vk
    vx
    @14
    vw
    cv
    #
    csn
    #
    cun
    #
    cB
    ciun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vx
    @23
    @5
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    vk
    vx
    cA
    cB
    ciun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vx
    cA
    @5
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    vy
    vz
    vw
    cA
    @0
    c0
    wceq
    #
    @3
    @10
    @7
    @12
    @35
    @2
    @9
    csumge0
    @35
    vk
    @1
    @8
    cC
    vx
    @0
    c0
    cB
    iuneq1
    mpteq1d
    fveq2d
    @35
    @6
    @11
    csumge0
    vx
    @0
    c0
    @5
    mpteq1
    fveq2d
    eqeq12d
    @0
    @14
    wceq
    #
    @3
    @17
    @7
    @19
    @36
    @2
    @16
    csumge0
    @36
    vk
    @1
    @15
    cC
    vx
    @0
    @14
    cB
    iuneq1
    mpteq1d
    fveq2d
    @36
    @6
    @18
    csumge0
    vx
    @0
    @14
    @5
    mpteq1
    fveq2d
    eqeq12d
    @0
    @23
    wceq
    #
    @3
    @26
    @7
    @28
    @37
    @2
    @25
    csumge0
    @37
    vk
    @1
    @24
    cC
    vx
    @0
    @23
    cB
    iuneq1
    mpteq1d
    fveq2d
    @37
    @6
    @27
    csumge0
    vx
    @0
    @23
    @5
    mpteq1
    fveq2d
    eqeq12d
    @0
    cA
    wceq
    #
    @3
    @32
    @7
    @34
    @38
    @2
    @31
    csumge0
    @38
    vk
    @1
    @30
    cC
    vx
    @0
    cA
    cB
    iuneq1
    mpteq1d
    fveq2d
    @38
    @6
    @33
    csumge0
    vx
    @0
    cA
    @5
    mpteq1
    fveq2d
    eqeq12d
    @13
    wph
    @10
    c0
    csumge0
    cfv
    @12
    @9
    c0
    csumge0
    @9
    vk
    c0
    cC
    cmpt
    #
    c0
    @8
    c0
    wceq
    @9
    @39
    wceq
    vx
    cB
    0iun
    vk
    @8
    c0
    cC
    mpteq1
    ax-mp
    vk
    cC
    mpt0
    eqtri
    fveq2i
    @11
    c0
    csumge0
    vx
    @5
    mpt0
    fveq2i
    eqtr4i
    a1i
    wph
    @14
    cA
    wss
    #
    @21
    cA
    @14
    cdif
    #
    wcel
    #
    wa
    #
    wa
    #
    @20
    @29
    @44
    @20
    wa
    #
    @14
    @5
    vx
    csu
    #
    vk
    vx
    @22
    cB
    ciun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    caddc
    co
    #
    @23
    @5
    vx
    csu
    #
    @26
    @28
    @44
    @50
    @51
    wceq
    @20
    @44
    @51
    @50
    @44
    @14
    @21
    @5
    @49
    vx
    @41
    @44
    vx
    nfv
    vx
    @48
    csumge0
    vx
    csumge0
    nfcv
    #
    vx
    vk
    @47
    cC
    vx
    @22
    cB
    nfiu1
    vx
    cC
    nfcv
    #
    nfmpt
    nffv
    wph
    @43
    @40
    @14
    cfn
    wcel
    #
    wph
    @40
    @42
    simprl
    #
    wph
    @40
    wa
    #
    cA
    cfn
    wcel
    #
    @40
    @54
    wph
    @57
    @40
    sge0iunmptlemfi.a
    adantr
    wph
    @40
    simpr
    cA
    @14
    ssfi
    syl2anc
    #
    syldan
    #
    wph
    @40
    @42
    simprr
    @44
    @14
    @22
    cin
    c0
    wceq
    #
    @21
    @14
    wcel
    wn
    #
    @43
    @60
    wph
    @42
    @60
    @40
    @42
    @61
    @60
    @21
    cA
    @14
    eldifn
    @14
    @21
    disjsn
    #
    sylibr
    adantl
    adantl
    #
    @62
    sylib
    wph
    @40
    vx
    cv
    #
    @14
    wcel
    #
    @5
    cc
    wcel
    @42
    @56
    @65
    wa
    #
    @5
    @66
    wph
    @64
    cA
    wcel
    #
    @5
    cr
    wcel
    #
    wph
    @40
    @65
    simpll
    #
    @40
    @65
    @67
    wph
    @14
    cA
    @64
    ssel2
    #
    adantll
    #
    sge0iunmptlemfi.re
    syl2anc
    #
    recnd
    adantlrr
    @64
    @21
    wceq
    #
    @4
    @48
    csumge0
    @73
    vk
    cB
    @47
    cC
    @73
    cB
    vx
    @21
    cB
    csb
    #
    @47
    vx
    @21
    cB
    csbeq1a
    #
    vx
    @21
    cB
    @74
    vx
    @21
    cB
    nfcsb1v
    #
    vw
    vex
    @75
    iunxsnf
    #
    syl6eqr
    mpteq1d
    #
    fveq2d
    @44
    @49
    wph
    @42
    @49
    cr
    wcel
    #
    @40
    wph
    @42
    wa
    #
    @49
    vk
    @74
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cr
    @80
    @48
    @81
    csumge0
    @48
    @81
    wceq
    @80
    vk
    @47
    @74
    cC
    @77
    mpteq1i
    #
    a1i
    fveq2d
    @42
    wph
    @21
    cA
    wcel
    #
    @82
    cr
    wcel
    #
    @21
    cA
    @14
    eldifi
    #
    wph
    @67
    wa
    #
    @68
    wi
    wph
    @84
    wa
    #
    @85
    wi
    vx
    vw
    @88
    @85
    vx
    @88
    vx
    nfv
    vx
    @82
    cr
    vx
    @81
    csumge0
    @52
    vx
    vk
    @74
    cC
    @76
    @53
    nfmpt
    nffv
    vx
    cr
    nfcv
    nfel
    nfim
    @73
    @87
    @88
    @68
    @85
    @73
    @67
    @84
    wph
    @64
    @21
    cA
    eleq1
    anbi2d
    @73
    @5
    @82
    cr
    @73
    @4
    @81
    csumge0
    @73
    @4
    @48
    @81
    @78
    @83
    syl6eq
    fveq2d
    eleq1d
    imbi12d
    sge0iunmptlemfi.re
    chvar
    sylan2
    eqeltrd
    adantrl
    #
    recnd
    fsumsplitsn
    eqcomd
    adantr
    @45
    @26
    @17
    @49
    cxad
    co
    #
    @46
    @49
    cxad
    co
    #
    @50
    @44
    @26
    @90
    wceq
    @20
    @44
    @26
    vk
    @15
    @47
    cun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    @90
    @26
    @94
    wceq
    @44
    @25
    @93
    csumge0
    vk
    @24
    @92
    cC
    vx
    @14
    @22
    cB
    iunxun
    mpteq1i
    fveq2i
    a1i
    @44
    vk
    @15
    @47
    cC
    cvv
    cvv
    @44
    vk
    nfv
    wph
    @40
    @15
    cvv
    wcel
    @42
    @56
    @15
    @30
    cvv
    wph
    @30
    cvv
    wcel
    #
    @40
    wph
    @57
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    @95
    sge0iunmptlemfi.a
    wph
    @96
    vx
    cA
    sge0iunmptlemfi.b
    ralrimiva
    vx
    cA
    cB
    cfn
    cV
    iunexg
    syl2anc
    #
    adantr
    @40
    @15
    @30
    wss
    wph
    vx
    @14
    cA
    cB
    iunss1
    adantl
    ssexd
    adantrr
    wph
    @42
    @47
    cvv
    wcel
    @40
    @80
    @47
    @30
    cvv
    wph
    @95
    @42
    @97
    adantr
    @42
    @47
    @30
    wss
    #
    wph
    @42
    @22
    cA
    wss
    #
    @98
    @42
    @84
    @99
    @86
    @21
    cA
    snssi
    syl
    #
    vx
    @22
    cA
    cB
    iunss1
    syl
    adantl
    ssexd
    adantrl
    @44
    vx
    cA
    cB
    wdisj
    #
    @40
    @99
    @60
    @15
    @47
    cin
    c0
    wceq
    wph
    @101
    @43
    sge0iunmptlemfi.dj
    adantr
    @55
    @42
    @99
    wph
    @40
    @100
    ad2antll
    @63
    vx
    cA
    cB
    @14
    @22
    disjiun
    syl13anc
    wph
    @40
    vk
    cv
    #
    @15
    wcel
    #
    cC
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @42
    @56
    @103
    wa
    @102
    cB
    wcel
    #
    vx
    @14
    wrex
    #
    @105
    @103
    @107
    @56
    @103
    @107
    vx
    @102
    @14
    cB
    eliun
    biimpi
    adantl
    @56
    @107
    @105
    wi
    @103
    @56
    @106
    @105
    vx
    @14
    @56
    @65
    @106
    @105
    @56
    @65
    @106
    w3a
    wph
    @67
    @106
    @105
    wph
    @40
    @65
    @106
    simp1l
    @56
    @65
    @67
    @106
    @71
    3adant3
    @56
    @65
    @106
    simp3
    sge0iunmptlemfi.c
    syl3anc
    3exp
    rexlimdv
    adantr
    mpd
    adantlrr
    wph
    @42
    @102
    @47
    wcel
    #
    @105
    @40
    @80
    @108
    wa
    @106
    vx
    @22
    wrex
    #
    @105
    @108
    @109
    @80
    @108
    @109
    vx
    @102
    @22
    cB
    eliun
    biimpi
    adantl
    @80
    @109
    @105
    wi
    @108
    @80
    @106
    @105
    vx
    @22
    @80
    @64
    @22
    wcel
    #
    @106
    @105
    @80
    @110
    @106
    w3a
    wph
    @67
    @106
    @105
    wph
    @42
    @110
    @106
    simp1l
    @80
    @110
    @67
    @106
    @42
    @110
    @67
    wph
    @42
    @22
    cA
    @64
    @100
    sselda
    adantll
    3adant3
    @80
    @110
    @106
    simp3
    sge0iunmptlemfi.c
    syl3anc
    3exp
    rexlimdv
    adantr
    mpd
    adantlrl
    sge0splitmpt
    eqtrd
    adantr
    @45
    @17
    @46
    @49
    cxad
    wph
    @40
    @20
    @17
    @46
    wceq
    @42
    @56
    @20
    wa
    @17
    @19
    @14
    @0
    @18
    cfv
    #
    vy
    csu
    #
    @46
    @20
    @20
    @56
    @20
    id
    adantl
    @56
    @19
    @112
    wceq
    @20
    @56
    vy
    @18
    @14
    @58
    @56
    vx
    @14
    @5
    cc0
    cpnf
    cico
    co
    #
    @18
    @66
    wph
    @67
    @5
    @113
    wcel
    #
    @69
    @71
    @87
    @68
    cc0
    @5
    cle
    wbr
    #
    wa
    @114
    @87
    @68
    @115
    sge0iunmptlemfi.re
    @87
    @4
    cV
    cB
    sge0iunmptlemfi.b
    @87
    vk
    cB
    cC
    @104
    @4
    wph
    @67
    @106
    @105
    sge0iunmptlemfi.c
    3expa
    @4
    eqid
    fmptd
    sge0ge0
    jca
    @5
    elrege0
    sylibr
    #
    syl2anc
    @18
    eqid
    #
    fmptd
    sge0fsum
    adantr
    @56
    @112
    @46
    wceq
    @20
    @56
    @112
    @14
    @64
    @18
    cfv
    #
    vx
    csu
    #
    @46
    @112
    @119
    wceq
    @56
    @14
    @111
    @118
    vy
    vx
    @0
    @64
    @18
    fveq2
    vx
    @14
    nfcv
    vy
    @14
    nfcv
    vx
    @0
    @18
    vx
    @14
    @5
    nfmpt1
    vx
    @0
    nfcv
    nffv
    vy
    @118
    nfcv
    cbvsum
    a1i
    @56
    @14
    @118
    @5
    vx
    @56
    @118
    @5
    wceq
    #
    vx
    @14
    @65
    @120
    @56
    @65
    @65
    @5
    cvv
    wcel
    @120
    @65
    id
    @65
    @4
    csumge0
    fvexd
    vx
    @14
    @5
    cvv
    @18
    @117
    fvmpt2
    syl2anc
    adantl
    ralrimiva
    sumeq2d
    eqtrd
    adantr
    3eqtrd
    adantlrr
    oveq1d
    @44
    @91
    @50
    wceq
    #
    @20
    @44
    @46
    cr
    wcel
    #
    @79
    @121
    wph
    @40
    @122
    @42
    @56
    @14
    @5
    vx
    @58
    @72
    fsumrecl
    adantrr
    @89
    @46
    @49
    rexadd
    syl2anc
    adantr
    3eqtrd
    @44
    @28
    @51
    wceq
    @20
    @44
    @23
    @5
    vx
    @44
    @54
    @22
    cfn
    wcel
    #
    @23
    cfn
    wcel
    @59
    @123
    @44
    @21
    snfi
    a1i
    @14
    @22
    unfi
    syl2anc
    @44
    @64
    @23
    wcel
    #
    wa
    wph
    @67
    @114
    wph
    @43
    @124
    simpll
    @43
    @124
    @67
    wph
    @43
    @124
    wa
    @65
    @67
    @40
    @65
    @67
    @42
    @124
    @70
    ad4ant14
    @42
    @124
    @65
    wn
    #
    @67
    @40
    @42
    @124
    wa
    @125
    wa
    @42
    @73
    @67
    @42
    @124
    @125
    simpll
    @124
    @125
    @73
    @42
    @124
    @125
    wa
    @110
    @73
    @64
    @14
    @22
    elunnel1
    @64
    @21
    elsni
    syl
    adantll
    @42
    @73
    wa
    @64
    @21
    cA
    @42
    @73
    simpr
    @42
    @84
    @73
    @86
    adantr
    eqeltrd
    syl2anc
    adantlll
    pm2.61dan
    adantll
    @116
    syl2anc
    sge0fsummpt
    adantr
    3eqtr4d
    ex
    sge0iunmptlemfi.a
    findcard2d
end
