include "cz.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "ccoe.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "cc.mm"
include "cdgr.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "a1i.mm"
include "wss.mm"
include "cn0.mm"
include "wf.mm"
include "zsscn.mm"
include "cle.mm"
include "wbr.mm"
include "dgrcl.mm"
include "syl.mm"
include "nn0zd.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "ssrab2.mm"
include "cuz.mm"
include "c0.mm"
include "nn0uz.mm"
include "sseqtri.mm"
include "c0p.mm"
include "neneqd.mm"
include "wb.mm"
include "eqid.mm"
include "dgreq0.mm"
include "mtbid.mm"
include "neqned.mm"
include "jca.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "elrab.mm"
include "sylibr.mm"
include "ne0i.mm"
include "infssuzcl.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "syl5eqel.mm"
include "zsubcld.mm"
include "infssuzle.mm"
include "eqbrtrd.mm"
include "nn0red.mm"
include "subge0d.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "caddc.mm"
include "id.mm"
include "0zd.mm"
include "coef2.mm"
include "adantr.mm"
include "simpr.mm"
include "nn0addcld.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "elplyr.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "cif.mm"
include "iftrued.mm"
include "wn.mm"
include "iffalse.mm"
include "adantl.mm"
include "wo.mm"
include "ad2antrr.mm"
include "resubcld.mm"
include "nn0re.mm"
include "ad2antlr.mm"
include "ltnled.mm"
include "ltsubaddd.mm"
include "mpbid.mm"
include "olc.mm"
include "dgrlt.mm"
include "simprd.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"
include "mpteq2dva.mm"
include "fssd.mm"
include "elfznn0.mm"
include "eqidd.mm"
include "simpl.mm"
include "fvmpt2d.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "sumeq12rdv.mm"
include "eqtrd.mm"
include "coeeq2.mm"
include "3eqtr4d.mm"
include "fveq1d.mm"
include "oveq1.mm"
include "addid2d.mm"
include "fveq2d.mm"
include "0nn0.mm"
include "fvmptd.mm"
include "3eqtrd.mm"
include "sylib.mm"
include "eqnetrd.mm"
include "cdiv.mm"
include "caa.mm"
include "aasscn.mm"
include "expcld.mm"
include "mulcld.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fsumshft.mm"
include "npcand.mm"
include "sumeq1d.mm"
include "elfzelz.mm"
include "expsubd.mm"
include "oveq2d.mm"
include "0red.mm"
include "zred.mm"
include "nn0ge0d.mm"
include "elfzle1.mm"
include "letrd.mm"
include "expne0d.mm"
include "divassd.mm"
include "eqcomd.mm"
include "eqtr2d.mm"
include "sumeq2dv.mm"
include "syl6eleq.mm"
include "fzss1.mm"
include "divcld.mm"
include "cdif.mm"
include "w3a.mm"
include "eldifi.mm"
include "3jca.mm"
include "lenltd.mm"
include "elfzle2.mm"
include "jca32.mm"
include "elfz2.mm"
include "eldifn.mm"
include "condan.mm"
include "neqne.mm"
include "adantll.mm"
include "mul02d.mm"
include "div0d.mm"
include "fzfid.mm"
include "fsumss.mm"
include "syldan.mm"
include "fvmpt2.mm"
include "fsumcl.mm"
include "coeid2.mm"
include "fsumdivc.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"

theorem elaa2lem
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let vj: setvar j
  let vx: setvar x
  assume elaa2lem.a: |- ( ph -> A e. AA )
  assume elaa2lem.an0: |- ( ph -> A =/= 0 )
  assume elaa2lem.g: |- ( ph -> G e. ( Poly ` ZZ ) )
  assume elaa2lem.gn0: |- ( ph -> G =/= 0p )
  assume elaa2lem.ga: |- ( ph -> ( G ` A ) = 0 )
  assume elaa2lem.m: |- M = inf ( { n e. NN0 | ( ( coeff ` G ) ` n ) =/= 0 } , RR , < )
  assume elaa2lem.i: |- I = ( k e. NN0 |-> ( ( coeff ` G ) ` ( k + M ) ) )
  assume elaa2lem.f: |- F = ( z e. CC |-> sum_ k e. ( 0 ... ( ( deg ` G ) - M ) ) ( ( I ` k ) x. ( z ^ k ) ) )

  disjoint A f
  disjoint A k
  disjoint A z
  disjoint k z
  disjoint F f
  disjoint G k
  disjoint G n
  disjoint G z
  disjoint I k
  disjoint I z
  disjoint M k
  disjoint M n
  disjoint M z
  disjoint k ph
  disjoint ph z
  disjoint A j
  disjoint j k
  disjoint G j
  disjoint j n
  disjoint M j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> E. f e. ( Poly ` ZZ ) ( ( ( coeff ` f ) ` 0 ) =/= 0 /\ ( f ` A ) = 0 ) )

  proof
    wph
    cF
    cz
    cply
    cfv
    #
    wcel
    cc0
    cF
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    cA
    cF
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    cc0
    vf
    cv
    #
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    cA
    @7
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vf
    @0
    wrex
    wph
    cF
    vz
    cc
    cc0
    cG
    cdgr
    cfv
    #
    cM
    cmin
    co
    #
    cfz
    co
    #
    vk
    cv
    #
    cI
    cfv
    #
    vz
    cv
    #
    @17
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    @0
    cF
    @23
    wceq
    wph
    elaa2lem.f
    a1i
    #
    wph
    cz
    cc
    wss
    #
    @15
    cn0
    wcel
    #
    cn0
    cz
    cI
    wf
    @23
    @0
    wcel
    @25
    wph
    zsscn
    a1i
    #
    wph
    @15
    cz
    wcel
    #
    cc0
    @15
    cle
    wbr
    #
    wa
    @26
    wph
    @28
    @29
    wph
    @14
    cM
    wph
    @14
    wph
    cG
    @0
    wcel
    #
    @14
    cn0
    wcel
    #
    elaa2lem.g
    cz
    cG
    dgrcl
    syl
    #
    nn0zd
    #
    wph
    cM
    wph
    cM
    vn
    cv
    #
    cG
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    vn
    cn0
    crab
    #
    cr
    clt
    cinf
    #
    cn0
    elaa2lem.m
    wph
    @38
    cn0
    @39
    @37
    vn
    cn0
    ssrab2
    #
    wph
    @38
    cc0
    cuz
    cfv
    #
    wss
    #
    @38
    c0
    wne
    #
    @39
    @38
    wcel
    @42
    wph
    @38
    cn0
    @41
    @40
    nn0uz
    sseqtri
    #
    a1i
    #
    wph
    @14
    @38
    wcel
    #
    @43
    wph
    @31
    @14
    @35
    cfv
    #
    cc0
    wne
    #
    wa
    @46
    wph
    @31
    @48
    @32
    wph
    @47
    cc0
    wph
    cG
    c0p
    wceq
    #
    @47
    cc0
    wceq
    #
    wph
    cG
    c0p
    elaa2lem.gn0
    neneqd
    wph
    @30
    @49
    @50
    wb
    elaa2lem.g
    @35
    cz
    cG
    @14
    @14
    eqid
    #
    @35
    eqid
    #
    dgreq0
    syl
    mtbid
    neqned
    jca
    @37
    @48
    vn
    @14
    cn0
    @34
    @14
    wceq
    @36
    @47
    cc0
    @34
    @14
    @35
    fveq2
    neeq1d
    elrab
    sylibr
    #
    @38
    @14
    ne0i
    syl
    @38
    cc0
    infssuzcl
    syl2anc
    #
    sseldi
    syl5eqel
    #
    nn0zd
    #
    zsubcld
    #
    wph
    @29
    cM
    @14
    cle
    wbr
    wph
    cM
    @39
    @14
    cle
    cM
    @39
    wceq
    #
    wph
    elaa2lem.m
    a1i
    #
    wph
    @42
    @46
    @39
    @14
    cle
    wbr
    @45
    @53
    @14
    @38
    cc0
    infssuzle
    syl2anc
    eqbrtrd
    wph
    @14
    cM
    wph
    @14
    @32
    nn0red
    #
    wph
    cM
    @55
    nn0red
    #
    subge0d
    mpbird
    jca
    @15
    elnn0z
    sylibr
    #
    wph
    vk
    cn0
    @17
    cM
    caddc
    co
    #
    @35
    cfv
    #
    cz
    cI
    wph
    @17
    cn0
    wcel
    #
    wa
    #
    cn0
    cz
    @63
    @35
    wph
    cn0
    cz
    @35
    wf
    #
    @65
    wph
    @30
    @67
    elaa2lem.g
    @30
    @30
    cc0
    cz
    wcel
    #
    @67
    @30
    id
    @30
    0zd
    #
    @35
    cz
    cG
    @52
    coef2
    syl2anc
    syl
    #
    adantr
    @66
    @17
    cM
    wph
    @65
    simpr
    wph
    cM
    cn0
    wcel
    #
    @65
    @55
    adantr
    nn0addcld
    #
    ffvelrnd
    #
    elaa2lem.i
    fmptd
    vz
    cI
    cz
    vk
    @15
    elplyr
    syl3anc
    eqeltrd
    #
    wph
    @3
    @5
    wph
    @2
    cM
    @35
    cfv
    #
    cc0
    wph
    @2
    cc0
    cI
    cfv
    @75
    @75
    wph
    cc0
    @1
    cI
    wph
    vk
    cn0
    @17
    @15
    cle
    wbr
    #
    @64
    cc0
    cif
    #
    cmpt
    vk
    cn0
    @64
    cmpt
    #
    @1
    cI
    wph
    vk
    cn0
    @77
    @64
    @66
    @76
    @77
    @64
    wceq
    @66
    @76
    wa
    @76
    @64
    cc0
    @66
    @76
    simpr
    iftrued
    @66
    @76
    wn
    #
    wa
    #
    @77
    cc0
    @64
    @79
    @77
    cc0
    wceq
    @66
    @76
    @64
    cc0
    iffalse
    adantl
    @80
    @14
    @63
    cle
    wbr
    #
    @64
    cc0
    wceq
    #
    @80
    @49
    @14
    @63
    clt
    wbr
    #
    wo
    #
    @81
    @82
    wa
    #
    @80
    @83
    @84
    @80
    @15
    @17
    clt
    wbr
    #
    @83
    @80
    @86
    @79
    @66
    @79
    simpr
    @80
    @15
    @17
    @80
    @14
    cM
    wph
    @14
    cr
    wcel
    @65
    @79
    @60
    ad2antrr
    #
    wph
    cM
    cr
    wcel
    #
    @65
    @79
    @61
    ad2antrr
    #
    resubcld
    @65
    @17
    cr
    wcel
    wph
    @79
    @17
    nn0re
    ad2antlr
    #
    ltnled
    mpbird
    @80
    @14
    cM
    @17
    @87
    @89
    @90
    ltsubaddd
    mpbid
    @83
    @49
    olc
    syl
    @80
    @30
    @63
    cn0
    wcel
    #
    @84
    @85
    wb
    wph
    @30
    @65
    @79
    elaa2lem.g
    ad2antrr
    @66
    @91
    @79
    @72
    adantr
    @35
    cz
    cG
    @63
    @14
    @51
    @52
    dgrlt
    syl2anc
    mpbid
    simprd
    eqtr4d
    pm2.61dan
    mpteq2dva
    wph
    vz
    @64
    cz
    vk
    cF
    @15
    @74
    @62
    wph
    @17
    @16
    wcel
    #
    wa
    #
    cn0
    cc
    @63
    @35
    wph
    cn0
    cc
    @35
    wf
    #
    @92
    wph
    cn0
    cz
    cc
    @35
    @70
    @27
    fssd
    #
    adantr
    @93
    @17
    cM
    @92
    @65
    wph
    @17
    @15
    elfznn0
    adantl
    #
    wph
    @71
    @92
    @55
    adantr
    nn0addcld
    ffvelrnd
    #
    wph
    cF
    @23
    vz
    cc
    @16
    @64
    @20
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    @24
    wph
    vz
    cc
    @22
    @99
    wph
    @19
    cc
    wcel
    #
    wa
    #
    @16
    @16
    @21
    @98
    vk
    @101
    @16
    eqidd
    @101
    @92
    wa
    @18
    @64
    @20
    cmul
    wph
    @92
    @18
    @64
    wceq
    #
    @100
    @93
    wph
    @65
    @102
    wph
    @92
    simpl
    #
    @96
    wph
    vk
    cn0
    @64
    cI
    cz
    cI
    @78
    wceq
    wph
    elaa2lem.i
    a1i
    #
    @73
    fvmpt2d
    syl2anc
    adantlr
    oveq1d
    sumeq12rdv
    mpteq2dva
    eqtrd
    coeeq2
    @104
    3eqtr4d
    fveq1d
    wph
    vk
    cc0
    @64
    @75
    cn0
    cI
    cz
    @104
    wph
    @17
    cc0
    wceq
    #
    wa
    #
    @63
    cM
    @35
    @106
    @63
    cc0
    cM
    caddc
    co
    #
    cM
    @105
    @63
    @107
    wceq
    wph
    @17
    cc0
    cM
    caddc
    oveq1
    adantl
    wph
    @107
    cM
    wceq
    @105
    wph
    cM
    wph
    cz
    cc
    cM
    zsscn
    @56
    sseldi
    #
    addid2d
    #
    adantr
    eqtrd
    fveq2d
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    wph
    cn0
    cz
    cM
    @35
    @70
    @55
    ffvelrnd
    fvmptd
    wph
    @75
    eqidd
    3eqtrd
    wph
    @71
    @75
    cc0
    wne
    #
    wph
    cM
    @38
    wcel
    @71
    @110
    wa
    wph
    cM
    @39
    @38
    @59
    @54
    eqeltrd
    @37
    @110
    vn
    cM
    cn0
    @34
    cM
    wceq
    @36
    @75
    cc0
    @34
    cM
    @35
    fveq2
    neeq1d
    elrab
    sylib
    simprd
    eqnetrd
    wph
    @4
    cA
    cG
    cfv
    #
    cA
    cM
    cexp
    co
    #
    cdiv
    co
    #
    cc0
    @112
    cdiv
    co
    #
    cc0
    wph
    @16
    @64
    cA
    @17
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    @14
    cfz
    co
    #
    vj
    cv
    #
    @35
    cfv
    #
    cA
    @119
    cexp
    co
    #
    cmul
    co
    #
    @112
    cdiv
    co
    #
    vj
    csu
    #
    @4
    @113
    wph
    @117
    @107
    @15
    cM
    caddc
    co
    #
    cfz
    co
    #
    @119
    cM
    cmin
    co
    #
    cM
    caddc
    co
    #
    @35
    cfv
    #
    cA
    @127
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    cM
    @14
    cfz
    co
    #
    @123
    vj
    csu
    #
    @124
    wph
    @116
    @131
    vk
    vj
    cM
    cc0
    @15
    @56
    wph
    @30
    @68
    elaa2lem.g
    @69
    syl
    @57
    @93
    @64
    @115
    @97
    @93
    cA
    @17
    @93
    wph
    cA
    cc
    wcel
    #
    @103
    wph
    caa
    cc
    cA
    aasscn
    elaa2lem.a
    sseldi
    #
    syl
    @96
    expcld
    mulcld
    #
    @17
    @127
    wceq
    #
    @64
    @129
    @115
    @130
    cmul
    @138
    @63
    @128
    @35
    @17
    @127
    cM
    caddc
    oveq1
    fveq2d
    @17
    @127
    cA
    cexp
    oveq2
    oveq12d
    fsumshft
    wph
    @132
    @133
    @131
    vj
    csu
    @134
    wph
    @126
    @133
    @131
    vj
    wph
    @107
    cM
    @125
    @14
    cfz
    @109
    wph
    @14
    cM
    wph
    cz
    cc
    @14
    zsscn
    @33
    sseldi
    @108
    npcand
    oveq12d
    sumeq1d
    wph
    @133
    @131
    @123
    vj
    wph
    @119
    @133
    wcel
    #
    wa
    #
    @131
    @120
    @130
    cmul
    co
    #
    @123
    @140
    @129
    @120
    @130
    cmul
    @140
    @128
    @119
    @35
    @140
    @119
    cM
    @140
    cz
    cc
    @119
    zsscn
    @139
    @119
    cz
    wcel
    #
    wph
    @119
    cM
    @14
    elfzelz
    adantl
    #
    sseldi
    wph
    cM
    cc
    wcel
    @139
    @108
    adantr
    npcand
    fveq2d
    oveq1d
    @140
    @141
    @120
    @121
    @112
    cdiv
    co
    #
    cmul
    co
    #
    @123
    @140
    @130
    @144
    @120
    cmul
    @140
    cA
    @119
    cM
    wph
    @135
    @139
    @136
    adantr
    #
    wph
    cA
    cc0
    wne
    @139
    elaa2lem.an0
    adantr
    #
    wph
    cM
    cz
    wcel
    #
    @139
    @56
    adantr
    #
    @143
    expsubd
    oveq2d
    @140
    @123
    @145
    @140
    @120
    @121
    @112
    @140
    cn0
    cc
    @119
    @35
    wph
    @94
    @139
    @95
    adantr
    @140
    @142
    cc0
    @119
    cle
    wbr
    #
    wa
    @119
    cn0
    wcel
    #
    @140
    @142
    @150
    @143
    @140
    cc0
    cM
    @119
    @140
    0red
    wph
    @88
    @139
    @61
    adantr
    @140
    @119
    @143
    zred
    wph
    cc0
    cM
    cle
    wbr
    @139
    wph
    cM
    @55
    nn0ge0d
    adantr
    @139
    cM
    @119
    cle
    wbr
    #
    wph
    @119
    cM
    @14
    elfzle1
    adantl
    letrd
    jca
    @119
    elnn0z
    sylibr
    #
    ffvelrnd
    #
    @140
    cA
    @119
    @146
    @153
    expcld
    #
    wph
    @112
    cc
    wcel
    @139
    wph
    cA
    cM
    @136
    @55
    expcld
    #
    adantr
    #
    @140
    cA
    cM
    @146
    @147
    @149
    expne0d
    #
    divassd
    eqcomd
    eqtr2d
    eqtr4d
    sumeq2dv
    eqtrd
    wph
    @133
    @118
    @123
    vj
    wph
    cM
    @41
    wcel
    @133
    @118
    wss
    wph
    cM
    cn0
    @41
    @55
    nn0uz
    syl6eleq
    cM
    cc0
    @14
    fzss1
    syl
    @140
    @122
    @112
    @140
    @120
    @121
    @154
    @155
    mulcld
    @157
    @158
    divcld
    wph
    @119
    @118
    @133
    cdif
    wcel
    #
    wa
    #
    @123
    @114
    cc0
    @160
    @122
    cc0
    @112
    cdiv
    @160
    @122
    cc0
    @121
    cmul
    co
    cc0
    @160
    @120
    cc0
    @121
    cmul
    @160
    @120
    cc0
    wceq
    #
    @119
    cM
    clt
    wbr
    #
    @160
    @162
    @161
    wn
    #
    @160
    @162
    @139
    @160
    @162
    wn
    #
    wa
    #
    @148
    @14
    cz
    wcel
    #
    @142
    w3a
    #
    @152
    @119
    @14
    cle
    wbr
    #
    wa
    wa
    @139
    @165
    @167
    @152
    @168
    @165
    @148
    @166
    @142
    wph
    @148
    @159
    @164
    @56
    ad2antrr
    wph
    @166
    @159
    @164
    @33
    ad2antrr
    @159
    @142
    wph
    @164
    @159
    @119
    @118
    wcel
    #
    @142
    @119
    @118
    @133
    eldifi
    #
    @169
    @119
    @119
    @14
    elfznn0
    #
    nn0zd
    syl
    #
    ad2antlr
    #
    3jca
    @165
    @152
    @164
    @160
    @164
    simpr
    @165
    cM
    @119
    wph
    @88
    @159
    @164
    @61
    ad2antrr
    @165
    @119
    @173
    zred
    lenltd
    mpbird
    @159
    @168
    wph
    @164
    @159
    @169
    @168
    @170
    @119
    cc0
    @14
    elfzle2
    syl
    ad2antlr
    jca32
    @119
    cM
    @14
    elfz2
    sylibr
    @159
    @139
    wn
    wph
    @164
    @119
    @118
    @133
    eldifn
    ad2antlr
    condan
    adantr
    @160
    @163
    wa
    #
    @152
    @164
    @174
    cM
    @39
    @119
    cle
    @58
    @174
    elaa2lem.m
    a1i
    @174
    @42
    @119
    @38
    wcel
    #
    @39
    @119
    cle
    wbr
    @42
    @174
    @44
    a1i
    @159
    @163
    @175
    wph
    @159
    @163
    wa
    #
    @151
    @120
    cc0
    wne
    #
    wa
    @175
    @176
    @151
    @177
    @159
    @151
    @163
    @159
    @169
    @151
    @170
    @171
    syl
    #
    adantr
    @163
    @177
    @159
    @120
    cc0
    neqne
    adantl
    jca
    @37
    @177
    vn
    @119
    cn0
    @34
    @119
    wceq
    @36
    @120
    cc0
    @34
    @119
    @35
    fveq2
    neeq1d
    elrab
    sylibr
    adantll
    @119
    @38
    cc0
    infssuzle
    syl2anc
    eqbrtrd
    @174
    cM
    @119
    wph
    @88
    @159
    @163
    @61
    ad2antrr
    @159
    @119
    cr
    wcel
    wph
    @163
    @159
    @119
    @172
    zred
    ad2antlr
    lenltd
    mpbid
    condan
    oveq1d
    @160
    @121
    @160
    cA
    @119
    wph
    @135
    @159
    @136
    adantr
    @159
    @151
    wph
    @178
    adantl
    expcld
    mul02d
    eqtrd
    oveq1d
    wph
    @114
    cc0
    wceq
    @159
    wph
    @112
    @156
    wph
    cA
    cM
    @136
    elaa2lem.an0
    @56
    expne0d
    #
    div0d
    #
    adantr
    eqtrd
    wph
    cc0
    @14
    fzfid
    #
    fsumss
    3eqtrd
    wph
    vz
    cA
    @22
    @117
    cc
    cF
    cc
    @24
    wph
    @19
    cA
    wceq
    #
    wa
    #
    @16
    @21
    @116
    vk
    @183
    @92
    wa
    @18
    @64
    @20
    @115
    cmul
    wph
    @92
    @102
    @182
    @93
    @65
    @64
    cz
    wcel
    #
    @102
    @96
    wph
    @92
    @65
    @184
    @96
    @73
    syldan
    vk
    cn0
    @64
    cz
    cI
    elaa2lem.i
    fvmpt2
    syl2anc
    adantlr
    @182
    @20
    @115
    wceq
    wph
    @92
    @19
    cA
    @17
    cexp
    oveq1
    ad2antlr
    oveq12d
    sumeq2dv
    @136
    wph
    @16
    @116
    vk
    wph
    cc0
    @15
    fzfid
    @137
    fsumcl
    fvmptd
    wph
    @113
    @118
    @122
    vj
    csu
    #
    @112
    cdiv
    co
    @124
    wph
    @111
    @185
    @112
    cdiv
    wph
    @30
    @135
    @111
    @185
    wceq
    elaa2lem.g
    @136
    @35
    cz
    vj
    cG
    @14
    cA
    @52
    @51
    coeid2
    syl2anc
    oveq1d
    wph
    @118
    @122
    @112
    vj
    @181
    @156
    wph
    @169
    wa
    #
    @120
    @121
    @186
    cn0
    cc
    @119
    @35
    wph
    @94
    @169
    @95
    adantr
    @169
    @151
    wph
    @171
    adantl
    #
    ffvelrnd
    @186
    cA
    @119
    wph
    @135
    @169
    @136
    adantr
    @187
    expcld
    mulcld
    @179
    fsumdivc
    eqtrd
    3eqtr4d
    wph
    @111
    cc0
    @112
    cdiv
    elaa2lem.ga
    oveq1d
    @180
    3eqtrd
    jca
    @13
    @6
    vf
    cF
    @0
    @7
    cF
    wceq
    #
    @10
    @3
    @12
    @5
    @188
    @9
    @2
    cc0
    @188
    cc0
    @8
    @1
    @7
    cF
    ccoe
    fveq2
    fveq1d
    neeq1d
    @188
    @11
    @4
    cc0
    cA
    @7
    cF
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl2anc
end
