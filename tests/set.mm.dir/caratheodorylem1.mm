include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "id.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "mpteq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "csn.mm"
include "cz.mm"
include "eluzel2.mm"
include "fzsn.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wa.mm"
include "cdm.mm"
include "cuni.mm"
include "come.mm"
include "adantr.mm"
include "eqid.mm"
include "wss.mm"
include "caragenss.mm"
include "wf.mm"
include "elsni.mm"
include "adantl.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "elssuni.mm"
include "omecl.mm"
include "fmptd.mm"
include "sge0sn.mm"
include "cvv.mm"
include "eqidd.mm"
include "ciun.mm"
include "iuneq1d.mm"
include "iunxsng.mm"
include "3eqtrrd.mm"
include "a1i.mm"
include "ovex.mm"
include "fvex.mm"
include "iunex.mm"
include "fvmptd.mm"
include "3eqtr4d.mm"
include "snidg.mm"
include "fvexd.mm"
include "cfzo.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1.mm"
include "imp.mm"
include "3adant1.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "elfzoel1.mm"
include "elfzoelz.mm"
include "peano2zd.mm"
include "3jca.mm"
include "zred.mm"
include "elfzole1.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "ltled.mm"
include "cr.mm"
include "leid.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "ssiun2s.mm"
include "cbviunv.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "eluz2.mm"
include "eqcomi.mm"
include "syl6eleq.mm"
include "eqcomd.mm"
include "sseqtrd.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "cun.mm"
include "nfcv.mm"
include "elfzouz.mm"
include "iunp1.mm"
include "eqtrd.mm"
include "difeq1d.mm"
include "c0.mm"
include "wdisj.mm"
include "cbvdisjv.mm"
include "sylib.mm"
include "fzssuz.mm"
include "sseqtri.mm"
include "wn.mm"
include "fzp1nel.mm"
include "eldifd.mm"
include "disjiun2.mm"
include "undif4.mm"
include "simpl.mm"
include "simpr.mm"
include "oveq2d.mm"
include "syl2anc.mm"
include "difid.mm"
include "uneq12d.mm"
include "un0.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "3adant3.mm"
include "wral.mm"
include "simpll.mm"
include "elfzelz.mm"
include "elfzle1.mm"
include "adantll.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "eqsstrd.mm"
include "caragensplit.mm"
include "elfzuz.mm"
include "fssd.mm"
include "sge0p1.mm"
include "oveq1d.mm"
include "3ad2ant3.mm"
include "sseli.mm"
include "adantlr.mm"
include "omexrcl.mm"
include "sstrd.mm"
include "xaddcomd.mm"
include "syl3anc.mm"
include "3exp.mm"
include "fzind2.mm"
include "sylc.mm"

theorem caratheodorylem1
  let wph: wff ph
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cO: class O
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume caratheodorylem1.o: |- ( ph -> O e. OutMeas )
  assume caratheodorylem1.s: |- S = ( CaraGen ` O )
  assume caratheodorylem1.z: |- Z = ( ZZ>= ` M )
  assume caratheodorylem1.e: |- ( ph -> E : Z --> S )
  assume caratheodorylem1.dj: |- ( ph -> Disj_ n e. Z ( E ` n ) )
  assume caratheodorylem1.g: |- G = ( n e. Z |-> U_ i e. ( M ... n ) ( E ` i ) )
  assume caratheodorylem1.n: |- ( ph -> N e. ( ZZ>= ` M ) )

  disjoint E i
  disjoint E n
  disjoint i n
  disjoint G i
  disjoint G n
  disjoint M i
  disjoint M n
  disjoint N i
  disjoint N n
  disjoint O i
  disjoint O n
  disjoint Z n
  disjoint i ph
  disjoint n ph
  disjoint E j
  disjoint i j
  disjoint j n
  disjoint G j
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint Z j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( O ` ( G ` N ) ) = ( sum^ ` ( n e. ( M ... N ) |-> ( O ` ( E ` n ) ) ) ) )

  proof
    wph
    cN
    cM
    cN
    cfz
    co
    #
    wcel
    #
    wph
    cN
    cG
    cfv
    #
    cO
    cfv
    #
    vn
    @0
    vn
    cv
    #
    cE
    cfv
    #
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    caratheodorylem1.n
    cM
    cN
    eluzfz2
    syl
    wph
    id
    wph
    vj
    cv
    #
    cG
    cfv
    #
    cO
    cfv
    #
    vn
    cM
    @12
    cfz
    co
    #
    @6
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wi
    wph
    cM
    cG
    cfv
    #
    cO
    cfv
    #
    vn
    cM
    cM
    cfz
    co
    #
    @6
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wi
    #
    wph
    vi
    cv
    #
    cG
    cfv
    #
    cO
    cfv
    #
    vn
    cM
    @26
    cfz
    co
    #
    @6
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wi
    #
    wph
    @26
    c1
    caddc
    co
    #
    cG
    cfv
    #
    cO
    cfv
    #
    vn
    cM
    @34
    cfz
    co
    #
    @6
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wi
    wph
    @9
    wi
    vj
    vi
    cN
    cM
    cN
    @12
    cM
    wceq
    #
    @18
    @24
    wph
    @41
    @14
    @20
    @17
    @23
    @41
    @13
    @19
    cO
    @12
    cM
    cG
    fveq2
    fveq2d
    @41
    @16
    @22
    csumge0
    @41
    vn
    @15
    @21
    @6
    @12
    cM
    cM
    cfz
    oveq2
    mpteq1d
    fveq2d
    eqeq12d
    imbi2d
    @12
    @26
    wceq
    #
    @18
    @32
    wph
    @42
    @14
    @28
    @17
    @31
    @42
    @13
    @27
    cO
    @12
    @26
    cG
    fveq2
    fveq2d
    @42
    @16
    @30
    csumge0
    @42
    vn
    @15
    @29
    @6
    @12
    @26
    cM
    cfz
    oveq2
    mpteq1d
    fveq2d
    eqeq12d
    imbi2d
    @12
    @34
    wceq
    #
    @18
    @40
    wph
    @43
    @14
    @36
    @17
    @39
    @43
    @13
    @35
    cO
    @12
    @34
    cG
    fveq2
    fveq2d
    @43
    @16
    @38
    csumge0
    @43
    vn
    @15
    @37
    @6
    @12
    @34
    cM
    cfz
    oveq2
    mpteq1d
    fveq2d
    eqeq12d
    imbi2d
    @12
    cN
    wceq
    #
    @18
    @9
    wph
    @44
    @14
    @3
    @17
    @8
    @44
    @13
    @2
    cO
    @12
    cN
    cG
    fveq2
    fveq2d
    @44
    @16
    @7
    csumge0
    @44
    vn
    @15
    @0
    @6
    @12
    cN
    cM
    cfz
    oveq2
    mpteq1d
    fveq2d
    eqeq12d
    imbi2d
    @25
    @11
    wph
    @23
    vn
    cM
    csn
    #
    @6
    cmpt
    #
    csumge0
    cfv
    cM
    @46
    cfv
    @20
    wph
    @22
    @46
    csumge0
    wph
    vn
    @21
    @45
    @6
    wph
    cM
    cz
    wcel
    #
    @21
    @45
    wceq
    wph
    @11
    @47
    caratheodorylem1.n
    cM
    cN
    eluzel2
    syl
    #
    cM
    fzsn
    syl
    #
    mpteq1d
    fveq2d
    wph
    cM
    @46
    cz
    @48
    wph
    vn
    @45
    @6
    cc0
    cpnf
    cicc
    co
    @46
    wph
    @4
    @45
    wcel
    #
    wa
    #
    @5
    cO
    cO
    cdm
    #
    cuni
    #
    wph
    cO
    come
    wcel
    #
    @50
    caratheodorylem1.o
    adantr
    #
    @53
    eqid
    #
    @51
    @5
    @52
    wcel
    #
    @5
    @53
    wss
    #
    @51
    cS
    @52
    @5
    @51
    @54
    cS
    @52
    wss
    #
    @55
    cS
    cO
    caratheodorylem1.s
    caragenss
    #
    syl
    @51
    cZ
    cS
    @4
    cE
    wph
    cZ
    cS
    cE
    wf
    #
    @50
    caratheodorylem1.e
    adantr
    @51
    @4
    cM
    cZ
    @50
    @4
    cM
    wceq
    #
    wph
    @4
    cM
    elsni
    adantl
    wph
    cM
    cZ
    wcel
    #
    @50
    wph
    cM
    @10
    cZ
    wph
    @47
    cM
    @10
    wcel
    @48
    cM
    uzid
    syl
    caratheodorylem1.z
    syl6eleqr
    #
    adantr
    eqeltrd
    ffvelrnd
    sseldd
    @5
    @52
    elssuni
    #
    syl
    omecl
    @46
    eqid
    fmptd
    sge0sn
    wph
    vn
    cM
    @6
    @20
    @45
    @46
    cvv
    wph
    @46
    eqidd
    wph
    @62
    wa
    #
    @5
    @19
    cO
    @66
    cM
    cE
    cfv
    #
    vi
    @21
    @26
    cE
    cfv
    #
    ciun
    #
    @5
    @19
    wph
    @67
    @69
    wceq
    @62
    wph
    @69
    vi
    @45
    @68
    ciun
    #
    @67
    @67
    wph
    vi
    @21
    @45
    @68
    @49
    iuneq1d
    wph
    @63
    @70
    @67
    wceq
    @64
    vi
    cM
    @68
    @67
    cZ
    @26
    cM
    cE
    fveq2
    iunxsng
    syl
    wph
    @67
    eqidd
    3eqtrrd
    adantr
    @62
    @5
    @67
    wceq
    wph
    @4
    cM
    cE
    fveq2
    adantl
    wph
    @19
    @69
    wceq
    @62
    wph
    vn
    cM
    vi
    cM
    @4
    cfz
    co
    #
    @68
    ciun
    #
    @69
    cZ
    cG
    cvv
    cG
    vn
    cZ
    @72
    cmpt
    #
    wceq
    wph
    caratheodorylem1.g
    a1i
    @62
    @72
    @69
    wceq
    wph
    @62
    vi
    @71
    @21
    @68
    @4
    cM
    cM
    cfz
    oveq2
    iuneq1d
    adantl
    @64
    @69
    cvv
    wcel
    wph
    vi
    @21
    @68
    cM
    cM
    cfz
    ovex
    @26
    cE
    fvex
    iunex
    a1i
    fvmptd
    adantr
    3eqtr4d
    fveq2d
    wph
    @63
    cM
    @45
    wcel
    @64
    cM
    cZ
    snidg
    syl
    wph
    @19
    cO
    fvexd
    fvmptd
    3eqtrrd
    a1i
    @26
    cM
    cN
    cfzo
    co
    wcel
    #
    @33
    wph
    @40
    @74
    @33
    wph
    w3a
    wph
    @74
    @32
    @40
    @74
    @33
    wph
    simp3
    @74
    @33
    wph
    simp1
    @33
    wph
    @32
    @74
    @33
    wph
    @32
    @33
    id
    imp
    3adant1
    wph
    @74
    @32
    w3a
    #
    @35
    @34
    cE
    cfv
    #
    cin
    #
    cO
    cfv
    #
    @35
    @76
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @76
    cO
    cfv
    #
    @28
    cxad
    co
    #
    @36
    @39
    wph
    @74
    @81
    @83
    wceq
    @32
    wph
    @74
    wa
    #
    @78
    @82
    @80
    @28
    cxad
    @84
    @77
    @76
    cO
    @84
    @76
    @35
    wss
    #
    @77
    @76
    wceq
    #
    @84
    @76
    vj
    @37
    @12
    cE
    cfv
    #
    ciun
    #
    @35
    @84
    @34
    @37
    wcel
    #
    @76
    @88
    wss
    @74
    @89
    wph
    @74
    @47
    @34
    cz
    wcel
    #
    @90
    w3a
    #
    cM
    @34
    cle
    wbr
    #
    @34
    @34
    cle
    wbr
    #
    wa
    wa
    @89
    @74
    @91
    @92
    @93
    @74
    @47
    @90
    @90
    @26
    cM
    cN
    elfzoel1
    #
    @74
    @26
    @26
    cM
    cN
    elfzoelz
    #
    peano2zd
    #
    @96
    3jca
    @74
    cM
    @34
    @74
    cM
    @94
    zred
    #
    @74
    @34
    @96
    zred
    #
    @74
    cM
    @26
    @34
    @97
    @74
    @26
    @95
    zred
    #
    @98
    @26
    cM
    cN
    elfzole1
    #
    @74
    @26
    @99
    ltp1d
    lelttrd
    ltled
    @74
    @34
    cr
    wcel
    @93
    @98
    @34
    leid
    syl
    jca32
    @34
    cM
    @34
    elfz2
    sylibr
    adantl
    vj
    @37
    @87
    @34
    @76
    @12
    @34
    cE
    fveq2
    #
    ssiun2s
    syl
    #
    @84
    @35
    @88
    @84
    vn
    @34
    vj
    @71
    @87
    ciun
    #
    @88
    cZ
    cG
    cvv
    cG
    vn
    cZ
    @103
    cmpt
    #
    wceq
    #
    @84
    cG
    @73
    @104
    caratheodorylem1.g
    vn
    cZ
    @72
    @103
    vi
    vj
    @71
    @68
    @87
    @26
    @12
    cE
    fveq2
    cbviunv
    mpteq2i
    eqtri
    #
    a1i
    @4
    @34
    wceq
    #
    @103
    @88
    wceq
    @84
    @107
    vj
    @71
    @37
    @87
    @4
    @34
    cM
    cfz
    oveq2
    iuneq1d
    adantl
    @84
    @34
    @10
    cZ
    @84
    @47
    @90
    @92
    w3a
    @34
    @10
    wcel
    @84
    @47
    @90
    @92
    wph
    @47
    @74
    @48
    adantr
    #
    @84
    @26
    @74
    @26
    cz
    wcel
    wph
    @95
    adantl
    #
    peano2zd
    #
    @84
    cM
    @34
    @84
    cM
    @108
    zred
    #
    @84
    @34
    @110
    zred
    #
    @84
    cM
    @26
    @34
    @111
    @84
    @26
    @109
    zred
    #
    @112
    @74
    cM
    @26
    cle
    wbr
    wph
    @100
    adantl
    @84
    @26
    @113
    ltp1d
    lelttrd
    ltled
    3jca
    cM
    @34
    eluz2
    sylibr
    cZ
    @10
    caratheodorylem1.z
    eqcomi
    #
    syl6eleq
    #
    @88
    cvv
    wcel
    @84
    vj
    @37
    @87
    cM
    @34
    cfz
    ovex
    @12
    cE
    fvex
    #
    iunex
    a1i
    fvmptd
    #
    eqcomd
    sseqtrd
    @85
    @86
    @76
    @35
    sseqin2
    biimpi
    syl
    fveq2d
    @84
    @79
    @27
    cO
    @84
    @79
    vj
    @29
    @87
    ciun
    #
    @76
    cun
    #
    @76
    cdif
    #
    @118
    @76
    @76
    cdif
    #
    cun
    #
    @27
    @84
    @35
    @119
    @76
    @84
    @35
    @88
    @119
    @117
    @84
    @87
    @76
    vj
    cM
    @26
    vj
    @76
    nfcv
    @74
    @26
    @10
    wcel
    wph
    @26
    cM
    cN
    elfzouz
    adantl
    #
    @101
    iunp1
    eqtrd
    difeq1d
    @84
    @122
    @120
    @84
    @118
    @76
    cin
    c0
    wceq
    @122
    @120
    wceq
    @84
    vj
    cZ
    @87
    @29
    @34
    @76
    wph
    vj
    cZ
    @87
    wdisj
    #
    @74
    wph
    vn
    cZ
    @5
    wdisj
    @124
    caratheodorylem1.dj
    vn
    vj
    cZ
    @5
    @87
    @4
    @12
    cE
    fveq2
    cbvdisjv
    sylib
    adantr
    @29
    cZ
    wss
    @84
    @29
    @10
    cZ
    cM
    @26
    fzssuz
    @114
    sseqtri
    #
    a1i
    @84
    @34
    cZ
    @29
    @115
    @74
    @34
    @29
    wcel
    wn
    #
    wph
    @126
    @74
    cM
    @26
    fzp1nel
    a1i
    adantl
    eldifd
    @101
    disjiun2
    @118
    @76
    @76
    undif4
    syl
    eqcomd
    @84
    @122
    @27
    c0
    cun
    #
    @27
    @84
    @118
    @27
    @121
    c0
    @84
    @27
    @118
    @84
    wph
    @26
    cZ
    wcel
    #
    @27
    @118
    wceq
    wph
    @74
    simpl
    #
    @84
    @26
    @10
    cZ
    @123
    @114
    syl6eleq
    #
    wph
    @128
    wa
    #
    vn
    @26
    @103
    @118
    cZ
    cG
    cvv
    @105
    @131
    @106
    a1i
    @131
    @4
    @26
    wceq
    #
    wa
    #
    vj
    @71
    @29
    @87
    @133
    @4
    @26
    cM
    cfz
    @131
    @132
    simpr
    oveq2d
    iuneq1d
    wph
    @128
    simpr
    @118
    cvv
    wcel
    @131
    vj
    @29
    @87
    cM
    @26
    cfz
    ovex
    @116
    iunex
    a1i
    fvmptd
    #
    syl2anc
    eqcomd
    @121
    c0
    wceq
    @84
    @76
    difid
    a1i
    uneq12d
    @127
    @27
    wceq
    @84
    @27
    un0
    a1i
    eqtrd
    3eqtrd
    fveq2d
    oveq12d
    3adant3
    wph
    @74
    @36
    @81
    wceq
    @32
    @84
    @81
    @36
    @84
    @35
    cS
    @76
    cO
    @53
    wph
    @54
    @74
    caratheodorylem1.o
    adantr
    #
    caratheodorylem1.s
    @56
    @84
    cZ
    cS
    @34
    cE
    wph
    @61
    @74
    caratheodorylem1.e
    adantr
    @115
    ffvelrnd
    @84
    @35
    @88
    @53
    @117
    @84
    @87
    @53
    wss
    #
    vj
    @37
    wral
    @88
    @53
    wss
    @84
    @136
    vj
    @37
    @84
    @12
    @37
    wcel
    #
    wa
    wph
    @12
    cZ
    wcel
    #
    @136
    wph
    @74
    @137
    simpll
    @74
    @137
    @138
    wph
    @74
    @137
    wa
    #
    @12
    @10
    cZ
    @139
    @47
    @12
    cz
    wcel
    #
    cM
    @12
    cle
    wbr
    #
    w3a
    @12
    @10
    wcel
    @139
    @47
    @140
    @141
    @74
    @47
    @137
    @94
    adantr
    @137
    @140
    @74
    @12
    cM
    @34
    elfzelz
    adantl
    @137
    @141
    @74
    @12
    cM
    @34
    elfzle1
    adantl
    3jca
    cM
    @12
    eluz2
    sylibr
    @114
    syl6eleq
    adantll
    wph
    @138
    wa
    #
    @87
    @52
    wcel
    @136
    @142
    cS
    @52
    @87
    wph
    @59
    @138
    wph
    @54
    @59
    caratheodorylem1.o
    @60
    syl
    #
    adantr
    wph
    cZ
    cS
    @12
    cE
    caratheodorylem1.e
    ffvelrnda
    sseldd
    @87
    @52
    elssuni
    syl
    #
    syl2anc
    ralrimiva
    vj
    @37
    @87
    @53
    iunss
    sylibr
    #
    eqsstrd
    caragensplit
    eqcomd
    3adant3
    @75
    @39
    @31
    @82
    cxad
    co
    #
    @28
    @82
    cxad
    co
    #
    @83
    wph
    @74
    @39
    @146
    wceq
    @32
    @84
    @6
    @82
    vn
    cM
    @26
    @123
    @84
    @4
    @37
    wcel
    #
    wa
    #
    @5
    cO
    @53
    @84
    @54
    @148
    @135
    adantr
    @56
    @149
    wph
    @4
    cZ
    wcel
    #
    @58
    @84
    wph
    @148
    @129
    adantr
    @148
    @150
    @84
    @148
    @4
    @10
    cZ
    @4
    cM
    @34
    elfzuz
    @114
    syl6eleq
    adantl
    wph
    @150
    wa
    @57
    @58
    wph
    cZ
    @52
    @4
    cE
    wph
    cZ
    cS
    @52
    cE
    caratheodorylem1.e
    @143
    fssd
    ffvelrnda
    @65
    syl
    syl2anc
    omecl
    @107
    @5
    @76
    cO
    @4
    @34
    cE
    fveq2
    fveq2d
    sge0p1
    3adant3
    @32
    wph
    @146
    @147
    wceq
    @74
    @32
    @31
    @28
    @82
    cxad
    @32
    @28
    @31
    @32
    id
    eqcomd
    oveq1d
    3ad2ant3
    wph
    @74
    @147
    @83
    wceq
    @32
    @84
    @28
    @82
    @84
    @27
    cO
    @53
    @135
    @56
    @84
    wph
    @128
    @27
    @53
    wss
    @129
    @130
    @131
    @27
    @118
    @53
    @134
    @131
    @136
    vj
    @29
    wral
    @118
    @53
    wss
    @131
    @136
    vj
    @29
    wph
    @12
    @29
    wcel
    #
    @136
    @128
    wph
    @151
    wa
    wph
    @138
    @136
    wph
    @151
    simpl
    @151
    @138
    wph
    @29
    cZ
    @12
    @125
    sseli
    adantl
    @144
    syl2anc
    adantlr
    ralrimiva
    vj
    @29
    @87
    @53
    iunss
    sylibr
    eqsstrd
    syl2anc
    omexrcl
    @84
    @76
    cO
    @53
    @135
    @56
    @84
    @76
    @88
    @53
    @102
    @145
    sstrd
    omexrcl
    xaddcomd
    3adant3
    3eqtrd
    3eqtr4d
    syl3anc
    3exp
    fzind2
    sylc
end
