include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wf1.mm"
include "cab.mm"
include "chash.mm"
include "cfv.mm"
include "cfa.mm"
include "cbc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wi.mm"
include "c1.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "f1eq2.mm"
include "wfn.mm"
include "f1fn.mm"
include "fn0.mm"
include "sylib.mm"
include "f10.mm"
include "f1eq1.mm"
include "mpbiri.mm"
include "impbii.mm"
include "velsn.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "abbi1dv.mm"
include "fveq2d.mm"
include "cvv.mm"
include "0ex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "fveq2.mm"
include "hash0.mm"
include "fac0.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "abbidv.mm"
include "cn0.mm"
include "hashcl.mm"
include "bcn0.mm"
include "syl.mm"
include "1t1e1.mm"
include "syl6req.mm"
include "wn.mm"
include "wa.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "wex.mm"
include "abn0.mm"
include "cdom.mm"
include "f1domg.mm"
include "adantr.mm"
include "cle.mm"
include "vex.mm"
include "hashunsng.mm"
include "adantl.mm"
include "breq1d.mm"
include "wb.mm"
include "simprl.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "simpl.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "cn.mm"
include "ad2antrl.mm"
include "nn0p1nn.mm"
include "nnred.mm"
include "nn0red.mm"
include "lenltd.mm"
include "3bitr3d.mm"
include "sylibd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "necon4ad.mm"
include "imp.mm"
include "cc.mm"
include "faccl.mm"
include "nncnd.mm"
include "mul01d.mm"
include "3eqtr4a.mm"
include "cz.mm"
include "wo.mm"
include "nnzd.mm"
include "simpr.mm"
include "olcd.mm"
include "bcval4.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "a1d.mm"
include "cmin.mm"
include "oveq2.mm"
include "simplrr.mm"
include "hashf1lem2.mm"
include "cdiv.mm"
include "peano2nn0.mm"
include "nn0sub2.mm"
include "nnne0d.mm"
include "divcld.mm"
include "divcan2d.mm"
include "nn0cnd.mm"
include "subcld.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "eqeltrd.mm"
include "eqeltrrd.mm"
include "cfz.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "elfz5.mm"
include "mpbird.mm"
include "bcval2.mm"
include "divdiv1d.mm"
include "3eqtr4d.mm"
include "peano2fzr.mm"
include "elfzle2.mm"
include "facnn2.mm"
include "oveq1d.mm"
include "syl5ibr.mm"
include "ltlecasei.mm"
include "expcom.mm"
include "a2d.mm"
include "findcard2s.mm"

theorem hashf1
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A f
  disjoint B f
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( # ` { f | f : A -1-1-> B } ) = ( ( ! ` ( # ` A ) ) x. ( ( # ` B ) _C ( # ` A ) ) ) )

  proof
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    #
    cA
    cB
    vf
    cv
    #
    wf1
    #
    vf
    cab
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cfa
    cfv
    #
    cB
    chash
    cfv
    #
    @5
    cbc
    co
    #
    cmul
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    cB
    @1
    wf1
    #
    vf
    cab
    #
    chash
    cfv
    #
    @11
    chash
    cfv
    #
    cfa
    cfv
    #
    @7
    @15
    cbc
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @0
    c1
    c1
    @7
    cc0
    cbc
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @0
    vy
    cv
    #
    cB
    @1
    wf1
    #
    vf
    cab
    #
    chash
    cfv
    #
    @23
    chash
    cfv
    #
    cfa
    cfv
    #
    @7
    @27
    cbc
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @0
    @23
    vz
    cv
    #
    csn
    #
    cun
    #
    cB
    @1
    wf1
    #
    vf
    cab
    #
    chash
    cfv
    #
    @34
    chash
    cfv
    #
    cfa
    cfv
    #
    @7
    @38
    cbc
    co
    #
    cmul
    co
    #
    wceq
    #
    wi
    @0
    @10
    wi
    vx
    vy
    vz
    cA
    @11
    c0
    wceq
    #
    @19
    @22
    @0
    @43
    @14
    c1
    @18
    @21
    @43
    @14
    c0
    csn
    #
    chash
    cfv
    #
    c1
    @43
    @13
    @44
    chash
    @43
    @12
    vf
    @44
    @43
    @12
    c0
    cB
    @1
    wf1
    #
    @1
    @44
    wcel
    #
    @11
    c0
    cB
    @1
    f1eq2
    @46
    @1
    c0
    wceq
    #
    @47
    @46
    @48
    @46
    @1
    c0
    wfn
    @48
    c0
    cB
    @1
    f1fn
    @1
    fn0
    sylib
    @48
    @46
    c0
    cB
    c0
    wf1
    cB
    f10
    c0
    cB
    @1
    c0
    f1eq1
    mpbiri
    impbii
    vf
    c0
    velsn
    bitr4i
    syl6bb
    abbi1dv
    fveq2d
    c0
    cvv
    wcel
    @45
    c1
    wceq
    0ex
    c0
    cvv
    hashsng
    ax-mp
    syl6eq
    @43
    @16
    c1
    @17
    @20
    cmul
    @43
    @16
    cc0
    cfa
    cfv
    c1
    @43
    @15
    cc0
    cfa
    @43
    @15
    c0
    chash
    cfv
    #
    cc0
    @11
    c0
    chash
    fveq2
    hash0
    syl6eq
    #
    fveq2d
    fac0
    syl6eq
    @43
    @15
    cc0
    @7
    cbc
    @50
    oveq2d
    oveq12d
    eqeq12d
    imbi2d
    @11
    @23
    wceq
    #
    @19
    @31
    @0
    @51
    @14
    @26
    @18
    @30
    @51
    @13
    @25
    chash
    @51
    @12
    @24
    vf
    @11
    @23
    cB
    @1
    f1eq2
    abbidv
    fveq2d
    @51
    @16
    @28
    @17
    @29
    cmul
    @51
    @15
    @27
    cfa
    @11
    @23
    chash
    fveq2
    #
    fveq2d
    @51
    @15
    @27
    @7
    cbc
    @52
    oveq2d
    oveq12d
    eqeq12d
    imbi2d
    @11
    @34
    wceq
    #
    @19
    @42
    @0
    @53
    @14
    @37
    @18
    @41
    @53
    @13
    @36
    chash
    @53
    @12
    @35
    vf
    @11
    @34
    cB
    @1
    f1eq2
    abbidv
    fveq2d
    @53
    @16
    @39
    @17
    @40
    cmul
    @53
    @15
    @38
    cfa
    @11
    @34
    chash
    fveq2
    #
    fveq2d
    @53
    @15
    @38
    @7
    cbc
    @54
    oveq2d
    oveq12d
    eqeq12d
    imbi2d
    @11
    cA
    wceq
    #
    @19
    @10
    @0
    @55
    @14
    @4
    @18
    @9
    @55
    @13
    @3
    chash
    @55
    @12
    @2
    vf
    @11
    cA
    cB
    @1
    f1eq2
    abbidv
    fveq2d
    @55
    @16
    @6
    @17
    @8
    cmul
    @55
    @15
    @5
    cfa
    @11
    cA
    chash
    fveq2
    #
    fveq2d
    @55
    @15
    @5
    @7
    cbc
    @56
    oveq2d
    oveq12d
    eqeq12d
    imbi2d
    @0
    @21
    c1
    c1
    cmul
    co
    c1
    @0
    @20
    c1
    c1
    cmul
    @0
    @7
    cn0
    wcel
    #
    @20
    c1
    wceq
    cB
    hashcl
    #
    @7
    bcn0
    syl
    oveq2d
    1t1e1
    syl6req
    @23
    cfn
    wcel
    #
    @32
    @23
    wcel
    wn
    #
    wa
    #
    @0
    @31
    @42
    @0
    @61
    @31
    @42
    wi
    #
    @0
    @61
    wa
    #
    @62
    @7
    @27
    c1
    caddc
    co
    #
    @63
    @7
    @64
    clt
    wbr
    #
    wa
    #
    @42
    @31
    @66
    @37
    @39
    cc0
    cmul
    co
    #
    @41
    @66
    @49
    cc0
    @37
    @67
    hash0
    @66
    @36
    c0
    chash
    @63
    @65
    @36
    c0
    wceq
    @63
    @65
    @36
    c0
    @36
    c0
    wne
    @35
    vf
    wex
    @63
    @65
    wn
    #
    @35
    vf
    abn0
    @63
    @35
    @68
    vf
    @63
    @35
    @34
    cB
    cdom
    wbr
    #
    @68
    @0
    @35
    @69
    wi
    @61
    @34
    cB
    cfn
    @1
    f1domg
    adantr
    @63
    @38
    @7
    cle
    wbr
    #
    @64
    @7
    cle
    wbr
    #
    @69
    @68
    @63
    @38
    @64
    @7
    cle
    @61
    @38
    @64
    wceq
    #
    @0
    @32
    cvv
    wcel
    @61
    @72
    wi
    vz
    vex
    @23
    @32
    cvv
    hashunsng
    ax-mp
    adantl
    #
    breq1d
    @63
    @34
    cfn
    wcel
    #
    @0
    @70
    @69
    wb
    @63
    @59
    @33
    cfn
    wcel
    @74
    @0
    @59
    @60
    simprl
    #
    @32
    snfi
    @23
    @33
    unfi
    sylancl
    #
    @0
    @61
    simpl
    #
    @34
    cB
    cfn
    hashdom
    syl2anc
    @63
    @64
    @7
    @63
    @64
    @63
    @27
    cn0
    wcel
    #
    @64
    cn
    wcel
    #
    @59
    @78
    @0
    @60
    @23
    hashcl
    ad2antrl
    #
    @27
    nn0p1nn
    syl
    #
    nnred
    #
    @63
    @7
    @0
    @57
    @61
    @58
    adantr
    #
    nn0red
    #
    lenltd
    3bitr3d
    sylibd
    exlimdv
    syl5bi
    necon4ad
    imp
    fveq2d
    @66
    @39
    @63
    @39
    cc
    wcel
    @65
    @63
    @39
    @63
    @38
    cn0
    wcel
    #
    @39
    cn
    wcel
    @63
    @74
    @85
    @76
    @34
    hashcl
    syl
    @38
    faccl
    syl
    nncnd
    adantr
    mul01d
    3eqtr4a
    @66
    @40
    cc0
    @39
    cmul
    @66
    @40
    @7
    @64
    cbc
    co
    #
    cc0
    @66
    @38
    @64
    @7
    cbc
    @63
    @72
    @65
    @73
    adantr
    oveq2d
    @66
    @57
    @64
    cz
    wcel
    @64
    cc0
    clt
    wbr
    #
    @65
    wo
    @86
    cc0
    wceq
    @63
    @57
    @65
    @83
    adantr
    @66
    @64
    @63
    @79
    @65
    @81
    adantr
    nnzd
    @66
    @65
    @87
    @63
    @65
    simpr
    olcd
    @64
    @7
    bcval4
    syl3anc
    eqtrd
    oveq2d
    eqtr4d
    a1d
    @31
    @42
    @63
    @71
    wa
    #
    @7
    @27
    cmin
    co
    #
    @26
    cmul
    co
    #
    @89
    @30
    cmul
    co
    #
    wceq
    @26
    @30
    @89
    cmul
    oveq2
    @88
    @37
    @90
    @41
    @91
    @88
    vz
    @23
    cB
    vf
    @63
    @59
    @71
    @75
    adantr
    @63
    @0
    @71
    @77
    adantr
    @0
    @59
    @60
    @71
    simplrr
    @63
    @71
    simpr
    #
    hashf1lem2
    @88
    @64
    cfa
    cfv
    #
    @7
    cfa
    cfv
    #
    @7
    @64
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    @93
    cdiv
    co
    #
    cmul
    co
    #
    @89
    @97
    @89
    cdiv
    co
    #
    cmul
    co
    #
    @41
    @91
    @88
    @99
    @97
    @101
    @88
    @97
    @93
    @88
    @94
    @96
    @88
    @94
    @88
    @57
    @94
    cn
    wcel
    @63
    @57
    @71
    @83
    adantr
    #
    @7
    faccl
    syl
    nncnd
    #
    @88
    @96
    @88
    @95
    cn0
    wcel
    #
    @96
    cn
    wcel
    @88
    @64
    cn0
    wcel
    #
    @57
    @71
    @104
    @88
    @78
    @105
    @63
    @78
    @71
    @80
    adantr
    #
    @27
    peano2nn0
    syl
    #
    @102
    @92
    @64
    @7
    nn0sub2
    syl3anc
    #
    @95
    faccl
    syl
    #
    nncnd
    #
    @88
    @96
    @109
    nnne0d
    #
    divcld
    #
    @88
    @93
    @88
    @105
    @93
    cn
    wcel
    @107
    @64
    faccl
    syl
    #
    nncnd
    #
    @88
    @93
    @113
    nnne0d
    #
    divcan2d
    @88
    @97
    @89
    @112
    @88
    @7
    @27
    @88
    @7
    @102
    nn0cnd
    #
    @88
    @27
    @106
    nn0cnd
    #
    subcld
    #
    @88
    @89
    @88
    @89
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    @89
    cn
    @88
    @89
    cc
    wcel
    c1
    cc
    wcel
    @120
    @89
    wceq
    @118
    ax-1cn
    @89
    c1
    npcan
    sylancl
    @88
    @119
    cn0
    wcel
    @120
    cn
    wcel
    @88
    @119
    @95
    cn0
    @88
    @7
    @27
    c1
    @116
    @117
    @88
    1cnd
    subsub4d
    #
    @108
    eqeltrd
    @119
    nn0p1nn
    syl
    eqeltrrd
    #
    nnne0d
    #
    divcan2d
    eqtr4d
    @88
    @39
    @93
    @40
    @98
    cmul
    @88
    @38
    @64
    cfa
    @63
    @72
    @71
    @73
    adantr
    #
    fveq2d
    @88
    @86
    @94
    @96
    @93
    cmul
    co
    cdiv
    co
    #
    @40
    @98
    @88
    @64
    cc0
    @7
    cfz
    co
    #
    wcel
    #
    @86
    @125
    wceq
    @88
    @127
    @71
    @92
    @88
    @64
    cc0
    cuz
    cfv
    #
    wcel
    @7
    cz
    wcel
    @127
    @71
    wb
    @88
    @64
    cn0
    @128
    @107
    nn0uz
    syl6eleq
    @88
    @7
    @102
    nn0zd
    @64
    cc0
    @7
    elfz5
    syl2anc
    mpbird
    #
    @64
    @7
    bcval2
    syl
    @88
    @38
    @64
    @7
    cbc
    @124
    oveq2d
    @88
    @94
    @96
    @93
    @103
    @110
    @114
    @111
    @115
    divdiv1d
    3eqtr4d
    oveq12d
    @88
    @30
    @100
    @89
    cmul
    @88
    @30
    @28
    @94
    @89
    cfa
    cfv
    #
    cdiv
    co
    #
    @28
    cdiv
    co
    #
    cmul
    co
    #
    @100
    @88
    @29
    @132
    @28
    cmul
    @88
    @29
    @94
    @130
    @28
    cmul
    co
    cdiv
    co
    #
    @132
    @88
    @27
    @126
    wcel
    #
    @29
    @134
    wceq
    @88
    @27
    @128
    wcel
    @127
    @135
    @88
    @27
    cn0
    @128
    @106
    nn0uz
    syl6eleq
    @129
    @27
    cc0
    @7
    peano2fzr
    syl2anc
    #
    @27
    @7
    bcval2
    syl
    @88
    @94
    @130
    @28
    @103
    @88
    @130
    @88
    @89
    cn0
    wcel
    #
    @130
    cn
    wcel
    @88
    @78
    @57
    @27
    @7
    cle
    wbr
    #
    @137
    @106
    @102
    @88
    @135
    @138
    @136
    @27
    cc0
    @7
    elfzle2
    syl
    @27
    @7
    nn0sub2
    syl3anc
    @89
    faccl
    syl
    #
    nncnd
    #
    @88
    @28
    @88
    @78
    @28
    cn
    wcel
    @106
    @27
    faccl
    syl
    #
    nncnd
    #
    @88
    @130
    @139
    nnne0d
    #
    @88
    @28
    @141
    nnne0d
    #
    divdiv1d
    eqtr4d
    oveq2d
    @88
    @131
    @94
    @96
    @89
    cmul
    co
    #
    cdiv
    co
    @133
    @100
    @88
    @130
    @145
    @94
    cdiv
    @88
    @130
    @119
    cfa
    cfv
    #
    @89
    cmul
    co
    #
    @145
    @88
    @89
    cn
    wcel
    @130
    @147
    wceq
    @122
    @89
    facnn2
    syl
    @88
    @146
    @96
    @89
    cmul
    @88
    @119
    @95
    cfa
    @121
    fveq2d
    oveq1d
    eqtrd
    oveq2d
    @88
    @131
    @28
    @88
    @94
    @130
    @103
    @140
    @143
    divcld
    @142
    @144
    divcan2d
    @88
    @94
    @96
    @89
    @103
    @110
    @118
    @111
    @123
    divdiv1d
    3eqtr4d
    eqtrd
    oveq2d
    3eqtr4d
    eqeq12d
    syl5ibr
    @84
    @82
    ltlecasei
    expcom
    a2d
    findcard2s
    imp
end
