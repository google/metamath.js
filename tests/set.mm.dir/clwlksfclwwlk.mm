include "cfusgr.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "cclwwlkn.mm"
include "cv.mm"
include "wi.mm"
include "cclwlks.mm"
include "wceq.mm"
include "rabeq2i.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "cupgr.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "usgrupgr.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "upgrclwlkcompim.mm"
include "sylan.mm"
include "cn0.mm"
include "lencl.mm"
include "cclwwlk.mm"
include "c0.mm"
include "wne.mm"
include "cedg.mm"
include "cmin.mm"
include "clsw.mm"
include "clwlksfclwwlk2wrd.mm"
include "ad2antlr.mm"
include "swrdcl.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "ffz0iswrd.mm"
include "3ad2ant1.mm"
include "prmnn.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "oveq2.mm"
include "feq2d.mm"
include "nnnn0d.mm"
include "ffz0hash.mm"
include "ex.mm"
include "cr.mm"
include "nnred.mm"
include "lep1d.mm"
include "wb.mm"
include "breq2.mm"
include "mpbird.mm"
include "syldc.mm"
include "syl6bi.mm"
include "3imp21.mm"
include "swrdn0.mm"
include "syl3anc.mm"
include "opeq2.mm"
include "oveq2d.mm"
include "neeq1d.mm"
include "3ad2ant2.mm"
include "3exp.mm"
include "imp.mm"
include "jca.mm"
include "c2.mm"
include "simp-5r.mm"
include "anim12ci.mm"
include "cuz.mm"
include "prmuz2.mm"
include "adantlr.mm"
include "cz.mm"
include "eluz2.mm"
include "2re.mm"
include "a1i.mm"
include "zre.mm"
include "peano2re.mm"
include "3jca.mm"
include "simpr.mm"
include "letr.mm"
include "syl12anc.mm"
include "3adant1.mm"
include "sylbi.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "3imtr4d.mm"
include "syl5com.mm"
include "impcom.mm"
include "simp-4r.mm"
include "crn.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "usgrf.mm"
include "anim1i.mm"
include "clwlkclwwlklem2.mm"
include "syl3an1.mm"
include "biid.mm"
include "edgval.mm"
include "eleq2i.mm"
include "ralbii.mm"
include "3anbi123i.mm"
include "sylibr.mm"
include "syl121anc.mm"
include "clwlksfclwwlk1hash.mm"
include "simp2.mm"
include "simp1.mm"
include "wss.mm"
include "elfzelz.mm"
include "peano2zm.mm"
include "id.mm"
include "lem1d.mm"
include "syl3anbrc.mm"
include "fzoss2.mm"
include "3syl.mm"
include "sselda.mm"
include "3adant2.mm"
include "swrd0fv.mm"
include "eqcomd.mm"
include "elfzom1elp1fzo.mm"
include "preq12d.mm"
include "sylc.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "clwlksfclwwlk2sswd.mm"
include "oveq1d.mm"
include "raleqdv.mm"
include "bitrd.mm"
include "biimpd.mm"
include "elfz2nn0.mm"
include "1zzd.mm"
include "nn0z.mm"
include "3adant3.mm"
include "simp3.mm"
include "nnge1.mm"
include "sylanb.mm"
include "elfz2.mm"
include "swrd0fvlsw.mm"
include "swrd0fv0.mm"
include "expcom.mm"
include "com23.mm"
include "syl6.mm"
include "com12.mm"
include "3anbi23d.mm"
include "mpbid.mm"
include "3simpc.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "isclwwlk.mm"
include "eqeq1d.mm"
include "biimpcd.mm"
include "isclwwlkn.mm"
include "exp31.mm"
include "exp41.mm"
include "mpancom.mm"
include "3impib.mm"
include "com14.mm"
include "mpd.mm"
include "com24.mm"
include "pm2.43i.mm"
include "fmptd.mm"

theorem clwlksfclwwlk
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let cW: class W
  let vx: setvar x
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint C c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint W c
  disjoint C i
  disjoint G x
  disjoint i x
  disjoint N i
  assert |- ( ( G e. FinUSGraph /\ N e. Prime ) -> F : C --> ( N ClWWalksN G ) )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cprime
    wcel
    #
    wa
    #
    vc
    cC
    cB
    cc0
    cA
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    cN
    cG
    cclwwlkn
    co
    #
    cF
    vc
    cv
    #
    cC
    wcel
    #
    @2
    @5
    @6
    wcel
    #
    @8
    @2
    @9
    wi
    #
    @8
    @7
    cG
    cclwlks
    cfv
    #
    wcel
    #
    @3
    cN
    wceq
    #
    wa
    @8
    @10
    wi
    #
    @13
    vc
    cC
    @11
    clwlksfclwwlk.c
    rabeq2i
    @12
    @13
    @14
    @12
    @2
    @8
    @13
    @9
    @2
    @12
    @8
    @13
    @9
    wi
    wi
    #
    @2
    @12
    wa
    cA
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    #
    cc0
    @3
    cfz
    co
    #
    cG
    cvtx
    cfv
    #
    cB
    wf
    #
    wa
    #
    vi
    cv
    #
    cA
    cfv
    @16
    cfv
    @23
    cB
    cfv
    #
    @23
    c1
    caddc
    co
    #
    cB
    cfv
    #
    cpr
    #
    wceq
    vi
    cc0
    @3
    cfzo
    co
    #
    wral
    #
    cc0
    cB
    cfv
    #
    @3
    cB
    cfv
    wceq
    #
    w3a
    #
    @15
    @2
    cG
    cupgr
    wcel
    #
    @12
    @32
    @0
    @33
    @1
    @0
    cG
    cusgr
    wcel
    #
    @33
    cG
    fusgrusgr
    #
    cG
    usgrupgr
    syl
    adantr
    cB
    vi
    cA
    cG
    @16
    @20
    @7
    @20
    eqid
    #
    @16
    eqid
    #
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    upgrclwlkcompim
    sylan
    @2
    @32
    @15
    wi
    @12
    @13
    @32
    @8
    @2
    @9
    @32
    @13
    @14
    @22
    @29
    @31
    @13
    @14
    wi
    #
    @18
    @21
    @29
    @31
    wa
    #
    @38
    wi
    #
    @3
    cn0
    wcel
    #
    @18
    @21
    @40
    wi
    @17
    cA
    lencl
    @41
    @18
    wa
    #
    @21
    @39
    @13
    @14
    @42
    @21
    wa
    #
    @39
    wa
    #
    @13
    wa
    #
    @8
    @2
    @9
    @45
    @8
    wa
    #
    @2
    wa
    #
    @5
    cG
    cclwwlk
    cfv
    wcel
    #
    @5
    chash
    cfv
    #
    cN
    wceq
    #
    @9
    @47
    @5
    @20
    cword
    #
    wcel
    #
    @5
    c0
    wne
    #
    wa
    #
    @23
    @5
    cfv
    #
    @25
    @5
    cfv
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    vi
    cc0
    @49
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @5
    clsw
    cfv
    #
    cc0
    @5
    cfv
    #
    cpr
    #
    @58
    wcel
    #
    w3a
    #
    @48
    @47
    @54
    @62
    @66
    wa
    #
    @67
    @47
    @52
    @53
    @47
    cB
    @51
    wcel
    #
    @52
    @8
    @69
    @45
    @2
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk2wrd
    #
    ad2antlr
    @20
    cB
    cc0
    @3
    swrdcl
    syl
    @46
    @2
    @53
    @45
    @2
    @53
    wi
    #
    @8
    @44
    @13
    @71
    @21
    @13
    @71
    wi
    @42
    @39
    @21
    @13
    @2
    @53
    @21
    @13
    @2
    w3a
    #
    @53
    cB
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    c0
    wne
    #
    @72
    @69
    cN
    cn
    wcel
    #
    cN
    cB
    chash
    cfv
    #
    cle
    wbr
    #
    @75
    @21
    @13
    @69
    @2
    @20
    @3
    cB
    ffz0iswrd
    3ad2ant1
    @2
    @21
    @76
    @13
    @1
    @76
    @0
    cN
    prmnn
    #
    adantl
    #
    3ad2ant3
    @13
    @21
    @2
    @78
    @13
    @21
    cc0
    cN
    cfz
    co
    #
    @20
    cB
    wf
    #
    @2
    @78
    wi
    @13
    @19
    @81
    @20
    cB
    @3
    cN
    cc0
    cfz
    oveq2
    feq2d
    @2
    @82
    @77
    cN
    c1
    caddc
    co
    #
    wceq
    #
    @78
    @2
    @82
    @84
    @2
    cN
    cn0
    wcel
    @82
    @84
    @2
    cN
    @80
    nnnn0d
    @20
    cB
    cN
    ffz0hash
    sylan
    ex
    @1
    @84
    @78
    wi
    @0
    @1
    @84
    @78
    @1
    @84
    wa
    #
    @78
    cN
    @83
    cle
    wbr
    #
    @85
    cN
    @1
    cN
    cr
    wcel
    @84
    @1
    cN
    @79
    nnred
    adantr
    lep1d
    @84
    @78
    @86
    wb
    @1
    @77
    @83
    cN
    cle
    breq2
    adantl
    mpbird
    ex
    adantl
    syldc
    syl6bi
    3imp21
    cN
    @20
    cB
    swrdn0
    syl3anc
    @13
    @21
    @53
    @75
    wb
    @2
    @13
    @5
    @74
    c0
    @13
    @4
    @73
    cB
    csubstr
    @3
    cN
    cc0
    opeq2
    oveq2d
    neeq1d
    3ad2ant2
    mpbird
    3exp
    ad2antlr
    imp
    adantr
    imp
    jca
    @47
    cB
    clsw
    cfv
    @30
    wceq
    #
    @62
    @66
    w3a
    #
    @68
    @47
    @87
    @27
    @58
    wcel
    #
    vi
    cc0
    @3
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @90
    cB
    cfv
    #
    @30
    cpr
    #
    @58
    wcel
    #
    w3a
    #
    @88
    @47
    @34
    @18
    wa
    #
    @21
    c2
    @77
    cle
    wbr
    #
    @39
    @96
    @46
    @18
    @2
    @34
    @41
    @18
    @21
    @39
    @13
    @8
    simp-5r
    @0
    @34
    @1
    @35
    adantr
    anim12ci
    @42
    @21
    @39
    @13
    @8
    @2
    simp-5r
    @2
    @46
    @98
    @1
    @46
    @98
    wi
    @0
    @1
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    @46
    @98
    cN
    prmuz2
    @45
    @100
    @98
    wi
    #
    @8
    @44
    @13
    @101
    @43
    @13
    @101
    wi
    #
    @39
    @43
    @77
    @3
    c1
    caddc
    co
    #
    wceq
    #
    @102
    @41
    @21
    @104
    @18
    @20
    cB
    @3
    ffz0hash
    adantlr
    @104
    @13
    @101
    @104
    @13
    wa
    #
    @3
    @99
    wcel
    #
    c2
    @103
    cle
    wbr
    #
    @100
    @98
    @106
    @107
    wi
    @105
    @106
    c2
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    c2
    @3
    cle
    wbr
    #
    w3a
    @107
    c2
    @3
    eluz2
    @109
    @110
    @107
    @108
    @109
    @110
    wa
    c2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @103
    cr
    wcel
    #
    w3a
    #
    @110
    @3
    @103
    cle
    wbr
    #
    @107
    @109
    @114
    @110
    @109
    @111
    @112
    @113
    @111
    @109
    2re
    a1i
    @3
    zre
    #
    @109
    @112
    @113
    @116
    @3
    peano2re
    syl
    3jca
    adantr
    @109
    @110
    simpr
    @109
    @115
    @110
    @109
    @3
    @116
    lep1d
    adantr
    @114
    @110
    @115
    wa
    @107
    c2
    @3
    @103
    letr
    imp
    syl12anc
    3adant1
    sylbi
    a1i
    @13
    @100
    @106
    wb
    #
    @104
    @117
    cN
    @3
    cN
    @3
    @99
    eleq1
    eqcoms
    adantl
    @104
    @98
    @107
    wb
    @13
    @77
    @103
    c2
    cle
    breq2
    adantr
    3imtr4d
    ex
    syl
    adantr
    imp
    adantr
    syl5com
    adantl
    impcom
    @43
    @39
    @13
    @8
    @2
    simp-4r
    @97
    @21
    @98
    wa
    #
    @39
    w3a
    @87
    @27
    @16
    crn
    #
    wcel
    #
    vi
    @91
    wral
    #
    @94
    @119
    wcel
    #
    w3a
    #
    @96
    @97
    @17
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    @20
    cpw
    c0
    csn
    cdif
    crab
    #
    @16
    wf1
    #
    @18
    wa
    @118
    @39
    @123
    @34
    @125
    @18
    vx
    @16
    cG
    @20
    @36
    @37
    usgrf
    anim1i
    cB
    @124
    vi
    @16
    cA
    @20
    clwlkclwwlklem2
    syl3an1
    @87
    @87
    @92
    @121
    @95
    @122
    @87
    biid
    @89
    @120
    vi
    @91
    @58
    @119
    @27
    cG
    edgval
    #
    eleq2i
    ralbii
    @58
    @119
    @94
    @126
    eleq2i
    3anbi123i
    sylibr
    syl121anc
    @47
    @92
    @62
    @95
    @66
    @87
    @47
    @92
    @59
    vi
    @91
    wral
    #
    @62
    @8
    @92
    @127
    wb
    @45
    @2
    @8
    @89
    @59
    vi
    @91
    @8
    @23
    @91
    wcel
    #
    wa
    @27
    @57
    @58
    @8
    @128
    @27
    @57
    wceq
    #
    @8
    @3
    cc0
    @77
    cfz
    co
    wcel
    #
    @69
    @128
    @129
    wi
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk1hash
    #
    @70
    @130
    @69
    @128
    @129
    @130
    @69
    @128
    w3a
    #
    @24
    @55
    @26
    @56
    @132
    @55
    @24
    @132
    @69
    @130
    @23
    @28
    wcel
    #
    @55
    @24
    wceq
    @130
    @69
    @128
    simp2
    #
    @130
    @69
    @128
    simp1
    #
    @130
    @128
    @133
    @69
    @130
    @91
    @28
    @23
    @130
    @109
    @3
    @90
    cuz
    cfv
    wcel
    #
    @91
    @28
    wss
    @3
    cc0
    @77
    elfzelz
    #
    @109
    @90
    cz
    wcel
    @109
    @90
    @3
    cle
    wbr
    @136
    @3
    peano2zm
    @109
    id
    @109
    @3
    @116
    lem1d
    @90
    @3
    eluz2
    syl3anbrc
    @90
    cc0
    @3
    fzoss2
    3syl
    sselda
    3adant2
    @23
    @3
    @20
    cB
    swrd0fv
    syl3anc
    eqcomd
    @132
    @69
    @130
    @25
    @28
    wcel
    #
    @26
    @56
    wceq
    @134
    @135
    @130
    @128
    @138
    @69
    @130
    @109
    @128
    @138
    @137
    @23
    @3
    elfzom1elp1fzo
    sylan
    3adant2
    @69
    @130
    @138
    w3a
    @56
    @26
    @25
    @3
    @20
    cB
    swrd0fv
    eqcomd
    syl3anc
    preq12d
    3exp
    sylc
    imp
    eleq1d
    ralbidva
    ad2antlr
    @47
    @59
    vi
    @91
    @61
    @47
    @90
    @60
    cc0
    cfzo
    @8
    @90
    @60
    wceq
    @45
    @2
    @8
    @3
    @49
    c1
    cmin
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk2sswd
    #
    oveq1d
    ad2antlr
    oveq2d
    raleqdv
    bitrd
    @47
    @94
    @65
    @58
    @2
    @46
    @94
    @65
    wceq
    #
    @1
    @46
    @140
    wi
    @0
    @46
    @1
    @140
    @45
    @8
    @1
    @140
    wi
    #
    @13
    @8
    @141
    wi
    @44
    @13
    @1
    @8
    @140
    @13
    @1
    @3
    cprime
    wcel
    #
    @8
    @140
    wi
    @1
    @142
    wi
    cN
    @3
    cN
    @3
    wceq
    @1
    @142
    cN
    @3
    cprime
    eleq1
    biimpd
    eqcoms
    @142
    @3
    cn
    wcel
    #
    @8
    @140
    @3
    prmnn
    @8
    @130
    @69
    @143
    @140
    wi
    @131
    @70
    @130
    @143
    @69
    @140
    @130
    @143
    @69
    @140
    wi
    #
    @130
    @143
    wa
    #
    @3
    c1
    @77
    cfz
    co
    wcel
    #
    @144
    @145
    c1
    cz
    wcel
    #
    @77
    cz
    wcel
    #
    @109
    w3a
    #
    c1
    @3
    cle
    wbr
    #
    @3
    @77
    cle
    wbr
    #
    wa
    #
    wa
    #
    @146
    @130
    @41
    @77
    cn0
    wcel
    #
    @151
    w3a
    #
    @143
    @153
    @3
    @77
    elfz2nn0
    @155
    @143
    wa
    @149
    @152
    @155
    @149
    @143
    @41
    @154
    @149
    @151
    @41
    @154
    wa
    #
    @147
    @148
    @109
    @156
    1zzd
    @154
    @148
    @41
    @77
    nn0z
    adantl
    @41
    @109
    @154
    @3
    nn0z
    adantr
    3jca
    3adant3
    adantr
    @155
    @151
    @143
    @150
    @41
    @154
    @151
    simp3
    @3
    nnge1
    anim12ci
    jca
    sylanb
    @3
    c1
    @77
    elfz2
    sylibr
    @69
    @146
    @140
    @69
    @146
    wa
    #
    @93
    @63
    @30
    @64
    @157
    @63
    @93
    @3
    @20
    cB
    swrd0fvlsw
    eqcomd
    @157
    @64
    @30
    @3
    @20
    cB
    swrd0fv0
    eqcomd
    preq12d
    expcom
    syl
    ex
    com23
    sylc
    syl5com
    syl6
    com23
    adantl
    imp
    com12
    adantl
    impcom
    eleq1d
    3anbi23d
    mpbid
    @87
    @62
    @66
    3simpc
    syl
    @54
    @62
    @66
    3anass
    sylanbrc
    vi
    @58
    cG
    @20
    @5
    @36
    @58
    eqid
    isclwwlk
    sylibr
    @46
    @50
    @2
    @45
    @8
    @50
    @13
    @8
    @50
    wi
    @44
    @8
    @13
    @50
    @8
    @3
    @49
    cN
    @139
    eqeq1d
    biimpcd
    adantl
    imp
    adantr
    cG
    cN
    @5
    isclwwlkn
    sylanbrc
    exp31
    exp41
    mpancom
    imp
    3impib
    com12
    com14
    adantr
    mpd
    expcom
    com24
    imp
    sylbi
    pm2.43i
    impcom
    clwlksfclwwlk.f
    fmptd
end
