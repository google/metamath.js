include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cinf.mm"
include "cmbf.mm"
include "clsp.mm"
include "wcel.mm"
include "wa.mm"
include "cima.mm"
include "cxr.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "wss.mm"
include "cz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "cpnf.mm"
include "wceq.mm"
include "uzsup.mm"
include "syl.mm"
include "adantr.mm"
include "limsupval2.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "imassrn.mm"
include "wf.mm"
include "anass1rs.mm"
include "eqid.mm"
include "fmptd.mm"
include "ltpnfd.mm"
include "limsupgre.mm"
include "syl3anc.mm"
include "frn.mm"
include "syl5ss.mm"
include "cdm.mm"
include "cin.mm"
include "fdm.mm"
include "ineq1d.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "ne0i.mm"
include "eqnetrd.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "leidd.mm"
include "wb.mm"
include "rexrd.mm"
include "limsuple.mm"
include "mpbid.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "wfn.mm"
include "limsupgf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "breq2.mm"
include "ralima.mm"
include "sylancr.mm"
include "mpbird.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "infxrre.mm"
include "cres.mm"
include "df-ima.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simplll.mm"
include "uztrn2.mm"
include "adantll.mm"
include "simpllr.mm"
include "syl12anc.mm"
include "dmmptd.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "adantlr.mm"
include "3syl.mm"
include "dm0rn0.mm"
include "sylib.mm"
include "wi.mm"
include "uzss.mm"
include "syl6sseqr.mm"
include "sseldi.mm"
include "limsupgle.mm"
include "syl211anc.mm"
include "sylc.mm"
include "resmptd.mm"
include "fveq1d.mm"
include "fvres.mm"
include "adantl.mm"
include "eqtr3d.mm"
include "breq1d.mm"
include "eluzle.mm"
include "biimt.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "ralrn.mm"
include "suprcl.mm"
include "eluz.mm"
include "biimprd.mm"
include "impr.mm"
include "syldan.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "suprub.mm"
include "syl31anc.mm"
include "expr.mm"
include "ralrimiva.mm"
include "suprleub.mm"
include "xrletrid.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "infeq1d.mm"
include "3eqtrd.mm"
include "simpll.mm"
include "ad2ant2lr.mm"
include "simprr.mm"
include "ralrnmpt.mm"
include "rexbidv.mm"
include "an32s.mm"
include "mbfsup.mm"
include "anasss.mm"
include "breq2d.mm"
include "mbfinf.mm"
include "eqeltrd.mm"

theorem mbflimsup
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  assume mbflimsup.1: |- Z = ( ZZ>= ` M )
  assume mbflimsup.2: |- G = ( x e. A |-> ( limsup ` ( n e. Z |-> B ) ) )
  assume mbflimsup.h: |- H = ( m e. RR |-> sup ( ( ( ( n e. Z |-> B ) " ( m [,) +oo ) ) i^i RR* ) , RR* , < ) )
  assume mbflimsup.3: |- ( ph -> M e. ZZ )
  assume mbflimsup.4: |- ( ( ph /\ x e. A ) -> ( limsup ` ( n e. Z |-> B ) ) e. RR )
  assume mbflimsup.5: |- ( ( ph /\ n e. Z ) -> ( x e. A |-> B ) e. MblFn )
  assume mbflimsup.6: |- ( ( ph /\ ( n e. Z /\ x e. A ) ) -> B e. RR )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B m
  disjoint n ph
  disjoint ph x
  disjoint M m
  disjoint m n
  disjoint m x
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint i k
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint i m
  disjoint i z
  disjoint B i
  disjoint k m
  disjoint k z
  disjoint B k
  disjoint m y
  disjoint m z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint H i
  disjoint H k
  disjoint H y
  disjoint H z
  disjoint i ph
  disjoint k ph
  disjoint ph y
  disjoint Z i
  disjoint Z k
  disjoint n z
  disjoint x z
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> G e. MblFn )

  proof
    wph
    cG
    vx
    cA
    vi
    cZ
    vn
    vi
    cv
    #
    cuz
    cfv
    #
    cB
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    cmpt
    #
    cmbf
    wph
    cG
    vx
    cA
    vn
    cZ
    cB
    cmpt
    #
    clsp
    cfv
    #
    cmpt
    @8
    mbflimsup.2
    wph
    vx
    cA
    @10
    @7
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @10
    cH
    cZ
    cima
    #
    cxr
    clt
    cinf
    #
    @13
    cr
    clt
    cinf
    #
    @7
    @12
    cZ
    vm
    @9
    cH
    cvv
    mbflimsup.h
    @9
    cvv
    wcel
    @12
    vn
    cZ
    cB
    cZ
    cM
    cuz
    cfv
    #
    cvv
    mbflimsup.1
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    cZ
    cr
    wss
    #
    @12
    cZ
    cz
    cr
    cZ
    @16
    cz
    mbflimsup.1
    cM
    uzssz
    eqsstri
    #
    zssre
    sstri
    #
    a1i
    #
    wph
    cZ
    cxr
    clt
    csup
    cpnf
    wceq
    #
    @11
    wph
    cM
    cz
    wcel
    #
    @21
    mbflimsup.3
    cM
    cZ
    mbflimsup.1
    uzsup
    syl
    adantr
    limsupval2
    @12
    @13
    cr
    wss
    @13
    c0
    wne
    #
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vz
    @13
    wral
    #
    vy
    cr
    wrex
    #
    @14
    @15
    wceq
    @12
    @13
    cH
    crn
    #
    cr
    cH
    cZ
    imassrn
    @12
    cr
    cr
    cH
    wf
    #
    @29
    cr
    wss
    @12
    @22
    cZ
    cr
    @9
    wf
    @10
    cpnf
    clt
    wbr
    @30
    wph
    @22
    @11
    mbflimsup.3
    adantr
    @12
    vn
    cZ
    cB
    cr
    @9
    wph
    vn
    cv
    #
    cZ
    wcel
    #
    @11
    cB
    cr
    wcel
    #
    mbflimsup.6
    anass1rs
    #
    @9
    eqid
    #
    fmptd
    @12
    @10
    mbflimsup.4
    ltpnfd
    vm
    @9
    cH
    cM
    cZ
    mbflimsup.h
    mbflimsup.1
    limsupgre
    syl3anc
    #
    cr
    cr
    cH
    frn
    syl
    syl5ss
    @12
    cH
    cdm
    #
    cZ
    cin
    #
    c0
    wne
    @23
    @12
    @38
    cZ
    c0
    @12
    @38
    cr
    cZ
    cin
    #
    cZ
    @12
    @37
    cr
    cZ
    @12
    @30
    @37
    cr
    wceq
    @36
    cr
    cr
    cH
    fdm
    syl
    ineq1d
    @17
    @39
    cZ
    wceq
    @19
    cZ
    cr
    sseqin2
    mpbi
    syl6eq
    @12
    cM
    cZ
    wcel
    #
    cZ
    c0
    wne
    wph
    @40
    @11
    wph
    cM
    @16
    cZ
    wph
    @22
    cM
    @16
    wcel
    mbflimsup.3
    cM
    uzid
    syl
    mbflimsup.1
    syl6eleqr
    adantr
    cZ
    cM
    ne0i
    syl
    eqnetrd
    @13
    c0
    @38
    c0
    cH
    cZ
    imadisj
    necon3bii
    sylibr
    @12
    @10
    cr
    wcel
    #
    @10
    @25
    cle
    wbr
    #
    vz
    @13
    wral
    #
    @28
    mbflimsup.4
    @12
    @43
    @10
    @24
    cH
    cfv
    #
    cle
    wbr
    #
    vy
    cZ
    wral
    #
    @17
    @12
    @45
    vy
    cr
    wral
    #
    @46
    @19
    @12
    @10
    @10
    cle
    wbr
    #
    @47
    @12
    @10
    mbflimsup.4
    leidd
    #
    @12
    @17
    cZ
    cxr
    @9
    wf
    #
    @10
    cxr
    wcel
    #
    @48
    @47
    wb
    @20
    @12
    vn
    cZ
    cB
    cxr
    @9
    @12
    @32
    wa
    cB
    @34
    rexrd
    @35
    fmptd
    #
    @12
    @10
    mbflimsup.4
    rexrd
    #
    @10
    cZ
    vy
    vm
    @9
    cH
    mbflimsup.h
    limsuple
    syl3anc
    mpbid
    @45
    vy
    cZ
    cr
    ssralv
    mpsyl
    @12
    cH
    cr
    wfn
    #
    @17
    @43
    @46
    wb
    cr
    cxr
    cH
    wf
    @54
    vm
    @9
    cH
    mbflimsup.h
    limsupgf
    cr
    cxr
    cH
    ffn
    ax-mp
    @20
    @42
    @45
    vz
    vy
    cr
    cZ
    cH
    @25
    @44
    @10
    cle
    breq2
    ralima
    sylancr
    mpbird
    @27
    @43
    vy
    @10
    cr
    @24
    @10
    wceq
    #
    @26
    @42
    vz
    @13
    @24
    @10
    @25
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    vy
    vz
    @13
    infxrre
    syl3anc
    @12
    cr
    @13
    @6
    clt
    @12
    @13
    cH
    cZ
    cres
    #
    crn
    @6
    cH
    cZ
    df-ima
    @12
    @56
    @5
    @12
    @56
    vi
    cZ
    @0
    cH
    cfv
    #
    cmpt
    #
    @5
    @12
    @56
    vi
    cr
    @57
    cmpt
    #
    cZ
    cres
    #
    @58
    @12
    cH
    @59
    cZ
    @12
    vi
    cr
    cr
    cH
    @36
    feqmptd
    reseq1d
    @17
    @60
    @58
    wceq
    @19
    vi
    cr
    cZ
    @57
    resmpt
    ax-mp
    syl6eq
    @12
    vi
    cZ
    @57
    @4
    @12
    @0
    cZ
    wcel
    #
    wa
    #
    @57
    @4
    @62
    @57
    @12
    @30
    @0
    cr
    wcel
    #
    @57
    cr
    wcel
    #
    @61
    @36
    cZ
    cr
    @0
    @19
    sseli
    cr
    cr
    @0
    cH
    ffvelrn
    syl2an
    #
    rexrd
    #
    @62
    @4
    @62
    @3
    cr
    wss
    #
    @3
    c0
    wne
    #
    @25
    @24
    cle
    wbr
    #
    vz
    @3
    wral
    #
    vy
    cr
    wrex
    #
    @4
    cr
    wcel
    #
    @62
    @1
    cr
    @2
    wf
    #
    @67
    @62
    vn
    @1
    cB
    cr
    @2
    @62
    @31
    @1
    wcel
    #
    wa
    wph
    @32
    @11
    @33
    wph
    @11
    @61
    @74
    simplll
    @61
    @74
    @32
    @12
    cM
    @31
    @0
    cZ
    mbflimsup.1
    uztrn2
    #
    adantll
    wph
    @11
    @61
    @74
    simpllr
    mbflimsup.6
    syl12anc
    #
    @2
    eqid
    #
    fmptd
    #
    @1
    cr
    @2
    frn
    syl
    #
    @62
    @2
    cdm
    #
    c0
    wne
    @68
    @62
    @80
    @1
    c0
    @62
    vn
    @2
    @1
    cB
    cr
    @77
    @76
    dmmptd
    @62
    @0
    cz
    wcel
    #
    @0
    @1
    wcel
    @1
    c0
    wne
    wph
    @61
    @81
    @11
    wph
    @61
    wa
    #
    @0
    @16
    wcel
    #
    @81
    @82
    @0
    cZ
    @16
    wph
    @61
    simpr
    mbflimsup.1
    syl6eleq
    #
    cM
    @0
    eluzelz
    syl
    #
    adantlr
    #
    @0
    uzid
    @1
    @0
    ne0i
    3syl
    eqnetrd
    @80
    c0
    @3
    c0
    @2
    dm0rn0
    necon3bii
    sylib
    #
    @62
    @64
    @25
    @57
    cle
    wbr
    #
    vz
    @3
    wral
    #
    @71
    @65
    @62
    @89
    vk
    cv
    #
    @2
    cfv
    #
    @57
    cle
    wbr
    #
    vk
    @1
    wral
    #
    @62
    @93
    @0
    @90
    cle
    wbr
    #
    @90
    @9
    cfv
    #
    @57
    cle
    wbr
    #
    wi
    #
    vk
    @1
    wral
    #
    @62
    @1
    cZ
    wss
    #
    @97
    vk
    cZ
    wral
    #
    @98
    @62
    @1
    @16
    cZ
    @62
    @83
    @1
    @16
    wss
    wph
    @61
    @83
    @11
    @84
    adantlr
    cM
    @0
    uzss
    syl
    mbflimsup.1
    syl6sseqr
    #
    @62
    @57
    @57
    cle
    wbr
    #
    @100
    @62
    @57
    @65
    leidd
    @62
    @17
    @50
    @63
    @57
    cxr
    wcel
    @102
    @100
    wb
    @17
    @62
    @19
    a1i
    #
    @12
    @50
    @61
    @52
    adantr
    #
    @62
    cZ
    cr
    @0
    @19
    @12
    @61
    simpr
    sseldi
    #
    @66
    @57
    cZ
    @0
    vk
    vm
    @9
    cH
    mbflimsup.h
    limsupgle
    syl211anc
    mpbid
    @97
    vk
    @1
    cZ
    ssralv
    sylc
    @62
    @92
    @97
    vk
    @1
    @62
    @90
    @1
    wcel
    #
    wa
    #
    @92
    @96
    @97
    @107
    @91
    @95
    @57
    cle
    @107
    @90
    @9
    @1
    cres
    #
    cfv
    #
    @91
    @95
    @107
    @90
    @108
    @2
    @107
    vn
    cZ
    @1
    cB
    @62
    @99
    @106
    @101
    adantr
    resmptd
    fveq1d
    @106
    @109
    @95
    wceq
    @62
    @90
    @1
    @9
    fvres
    adantl
    eqtr3d
    #
    breq1d
    @107
    @94
    @96
    @97
    wb
    @106
    @94
    @62
    @0
    @90
    eluzle
    adantl
    @94
    @96
    biimt
    syl
    bitrd
    ralbidva
    mpbird
    @62
    @73
    @2
    @1
    wfn
    #
    @89
    @93
    wb
    @78
    @1
    cr
    @2
    ffn
    #
    @88
    @92
    vz
    vk
    @1
    @2
    @25
    @91
    @57
    cle
    breq1
    ralrn
    3syl
    mpbird
    #
    @70
    @89
    vy
    @57
    cr
    @24
    @57
    wceq
    @69
    @88
    vz
    @3
    @24
    @57
    @25
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    vy
    vz
    @3
    suprcl
    syl3anc
    #
    rexrd
    #
    @62
    @57
    @4
    cle
    wbr
    #
    @94
    @95
    @4
    cle
    wbr
    #
    wi
    #
    vk
    cZ
    wral
    #
    @62
    @119
    vk
    cZ
    @62
    @90
    cZ
    wcel
    #
    @94
    @118
    @62
    @121
    @94
    wa
    #
    wa
    #
    @67
    @68
    @71
    @95
    @3
    wcel
    @118
    @62
    @67
    @122
    @79
    adantr
    @62
    @68
    @122
    @87
    adantr
    @62
    @71
    @122
    @114
    adantr
    @123
    @91
    @95
    @3
    @62
    @122
    @106
    @91
    @95
    wceq
    @62
    @121
    @94
    @106
    @62
    @121
    wa
    @106
    @94
    @62
    @81
    @90
    cz
    wcel
    @106
    @94
    wb
    @121
    @86
    cZ
    cz
    @90
    @18
    sseli
    @0
    @90
    eluz
    syl2an
    biimprd
    impr
    #
    @110
    syldan
    @123
    @111
    @106
    @91
    @3
    wcel
    @123
    @73
    @111
    @62
    @73
    @122
    @78
    adantr
    @112
    syl
    @124
    @1
    @90
    @2
    fnfvelrn
    syl2anc
    eqeltrrd
    vy
    vz
    @3
    @95
    suprub
    syl31anc
    expr
    ralrimiva
    @62
    @17
    @50
    @63
    @4
    cxr
    wcel
    @117
    @120
    wb
    @103
    @104
    @105
    @116
    @4
    cZ
    @0
    vk
    vm
    @9
    cH
    mbflimsup.h
    limsupgle
    syl211anc
    mpbird
    @62
    @4
    @57
    cle
    wbr
    #
    @89
    @113
    @62
    @67
    @68
    @71
    @64
    @125
    @89
    wb
    @79
    @87
    @114
    @65
    vy
    vz
    vz
    @3
    @57
    suprleub
    syl31anc
    mpbird
    xrletrid
    #
    mpteq2dva
    eqtrd
    rneqd
    syl5eq
    infeq1d
    3eqtrd
    mpteq2dva
    syl5eq
    wph
    vx
    vy
    cA
    @4
    vi
    @8
    cM
    cZ
    mbflimsup.1
    @8
    eqid
    mbflimsup.3
    @82
    vx
    vy
    cA
    cB
    vn
    vx
    cA
    @4
    cmpt
    #
    @0
    @1
    @1
    eqid
    @127
    eqid
    @85
    @82
    @74
    wa
    wph
    @32
    vx
    cA
    cB
    cmpt
    cmbf
    wcel
    wph
    @61
    @74
    simpll
    @61
    @74
    @32
    wph
    @75
    adantll
    mbflimsup.5
    syl2anc
    @82
    @74
    @11
    wa
    #
    wa
    wph
    @32
    @11
    @33
    wph
    @61
    @128
    simpll
    @61
    @74
    @32
    wph
    @11
    @75
    ad2ant2lr
    @82
    @74
    @11
    simprr
    mbflimsup.6
    syl12anc
    wph
    @11
    @61
    cB
    @24
    cle
    wbr
    #
    vn
    @1
    wral
    #
    vy
    cr
    wrex
    #
    @62
    @71
    @131
    @114
    @62
    @70
    @130
    vy
    cr
    @62
    @33
    vn
    @1
    wral
    @70
    @130
    wb
    @62
    @33
    vn
    @1
    @76
    ralrimiva
    @69
    @129
    vn
    vz
    @1
    cB
    @2
    cr
    @77
    @25
    cB
    @24
    cle
    breq1
    ralrnmpt
    syl
    rexbidv
    mpbid
    an32s
    mbfsup
    wph
    @61
    @11
    @72
    wph
    @11
    @61
    @72
    @115
    an32s
    anasss
    @12
    @41
    @10
    @4
    cle
    wbr
    #
    vi
    cZ
    wral
    #
    @24
    @4
    cle
    wbr
    #
    vi
    cZ
    wral
    #
    vy
    cr
    wrex
    mbflimsup.4
    @12
    @10
    @57
    cle
    wbr
    #
    vi
    cZ
    wral
    #
    @133
    @17
    @12
    @136
    vi
    cr
    wral
    #
    @137
    @19
    @12
    @48
    @138
    @49
    @12
    @17
    @50
    @51
    @48
    @138
    wb
    @20
    @52
    @53
    @10
    cZ
    vi
    vm
    @9
    cH
    mbflimsup.h
    limsuple
    syl3anc
    mpbid
    @136
    vi
    cZ
    cr
    ssralv
    mpsyl
    @12
    @136
    @132
    vi
    cZ
    @62
    @57
    @4
    @10
    cle
    @126
    breq2d
    ralbidva
    mpbid
    @135
    @133
    vy
    @10
    cr
    @55
    @134
    @132
    vi
    cZ
    @24
    @10
    @4
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    mbfinf
    eqeltrd
end
