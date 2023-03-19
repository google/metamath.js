include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "cin.mm"
include "cn0.mm"
include "wa.mm"
include "wi.mm"
include "eldiophelnn0.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "cz.mm"
include "caddc.mm"
include "cuz.mm"
include "cdif.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cmzp.mm"
include "cn.mm"
include "cvv.mm"
include "cfn.mm"
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "id.mm"
include "zex.mm"
include "difexg.mm"
include "mp1i.mm"
include "com.mm"
include "ominf.mm"
include "cen.mm"
include "wbr.mm"
include "nn0z.mm"
include "lzenom.mm"
include "enfi.mm"
include "3syl.mm"
include "mtbiri.mm"
include "fz1eqin.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "eldioph2b.mm"
include "syl22anc.mm"
include "nnex.mm"
include "a1i.mm"
include "1z.mm"
include "nnuz.mm"
include "uzinf.mm"
include "elfznn.mm"
include "ssriv.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "c2.mm"
include "cexp.mm"
include "cmpt.mm"
include "inab.mm"
include "cun.mm"
include "simplrl.mm"
include "simplrr.mm"
include "eqcomd.mm"
include "reseq2d.mm"
include "ad3antrrr.mm"
include "simprrl.mm"
include "simprll.mm"
include "3eqtr2d.mm"
include "eqtr4d.mm"
include "elmapresaun.mm"
include "syl3anc.mm"
include "uneq2i.mm"
include "cle.mm"
include "nn0p1nn.mm"
include "nnge1d.mm"
include "lzunuz.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "unidm.mm"
include "uneq12d.mm"
include "syl5eqr.mm"
include "resundir.mm"
include "syl6eqr.mm"
include "uncom.mm"
include "reseq1i.mm"
include "incom.mm"
include "elmapresaunres2.mm"
include "fveq2d.mm"
include "simprlr.mm"
include "eqtrd.mm"
include "simprrr.mm"
include "jca32.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "simpr.mm"
include "difss.mm"
include "elmapssres.mm"
include "sylancl.mm"
include "adantr.mm"
include "nnssz.mm"
include "simprl.mm"
include "resabs1d.mm"
include "jca.mm"
include "resabs1.mm"
include "fveq2.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "rspc2ev.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "cr.mm"
include "wf.mm"
include "mzpf.mm"
include "syl.mm"
include "nn0ssz.mm"
include "mapss.mm"
include "mp2an.mm"
include "sseli.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "zred.mm"
include "sumsqeq0.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "syl5bbr.mm"
include "abbidv.mm"
include "simpl.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "sstri.mm"
include "pm3.2i.mm"
include "mzpresrename.mm"
include "2nn0.mm"
include "mzpexpmpt.mm"
include "simprr.mm"
include "mzpaddmpt.mm"
include "eldioph2.mm"
include "eqeltrd.mm"
include "ineq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "anabsi5.mm"

theorem diophin
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g


  assert |- ( ( A e. ( Dioph ` N ) /\ B e. ( Dioph ` N ) ) -> ( A i^i B ) e. ( Dioph ` N ) )

  proof
    cA
    cN
    cdioph
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    cin
    #
    @0
    wcel
    #
    @1
    cN
    cn0
    wcel
    #
    @1
    @2
    wa
    #
    @4
    wi
    cA
    cN
    eldiophelnn0
    @5
    @6
    cA
    vc
    cv
    #
    vd
    cv
    #
    c1
    cN
    cfz
    co
    #
    cres
    #
    wceq
    #
    @8
    va
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vd
    cn0
    cz
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cdif
    #
    cmap
    co
    #
    wrex
    #
    vc
    cab
    #
    wceq
    #
    va
    @18
    cmzp
    cfv
    #
    wrex
    #
    cB
    @7
    ve
    cv
    #
    @9
    cres
    #
    wceq
    #
    @25
    vb
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    ve
    cn0
    cn
    cmap
    co
    #
    wrex
    #
    vc
    cab
    #
    wceq
    #
    vb
    cn
    cmzp
    cfv
    #
    wrex
    #
    wa
    #
    @4
    @5
    @1
    @24
    @2
    @37
    @5
    @5
    @18
    cvv
    wcel
    #
    @18
    cfn
    wcel
    #
    wn
    @9
    @18
    wss
    #
    @1
    @24
    wb
    @5
    id
    #
    cz
    cvv
    wcel
    #
    @39
    @5
    zex
    cz
    @17
    cvv
    difexg
    mp1i
    @5
    @40
    com
    cfn
    wcel
    #
    ominf
    @5
    cN
    cz
    wcel
    #
    @18
    com
    cen
    wbr
    @40
    @44
    wb
    cN
    nn0z
    #
    cN
    lzenom
    @18
    com
    enfi
    3syl
    mtbiri
    @5
    @9
    @18
    cn
    cin
    #
    @18
    cN
    fz1eqin
    #
    @18
    cn
    inss1
    syl6eqss
    #
    vd
    vc
    cA
    @18
    cN
    va
    eldioph2b
    syl22anc
    @5
    @5
    cn
    cvv
    wcel
    #
    cn
    cfn
    wcel
    wn
    #
    @9
    cn
    wss
    #
    @2
    @37
    wb
    @42
    @50
    @5
    nnex
    a1i
    c1
    cz
    wcel
    #
    @51
    @5
    1z
    c1
    cn
    nnuz
    uzinf
    mp1i
    @52
    @5
    va
    @9
    cn
    @12
    cN
    elfznn
    ssriv
    #
    a1i
    ve
    vc
    cB
    cn
    cN
    vb
    eldioph2b
    syl22anc
    anbi12d
    @38
    @22
    @35
    wa
    #
    vb
    @36
    wrex
    va
    @23
    wrex
    @5
    @4
    @22
    @35
    va
    vb
    @23
    @36
    reeanv
    @5
    @55
    @4
    va
    vb
    @23
    @36
    @5
    @12
    @23
    wcel
    #
    @28
    @36
    wcel
    #
    wa
    #
    wa
    #
    @4
    @55
    @21
    @34
    cin
    #
    @0
    wcel
    @59
    @60
    @7
    vf
    cv
    #
    @9
    cres
    #
    wceq
    #
    @61
    vg
    cz
    cz
    cmap
    co
    #
    vg
    cv
    #
    @18
    cres
    #
    @12
    cfv
    #
    c2
    cexp
    co
    #
    @65
    cn
    cres
    #
    @28
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmpt
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vf
    cn0
    cz
    cmap
    co
    #
    wrex
    #
    vc
    cab
    #
    @0
    @59
    @60
    @20
    @33
    wa
    #
    vc
    cab
    @79
    @20
    @33
    vc
    inab
    @59
    @80
    @78
    vc
    @80
    @15
    @31
    wa
    #
    ve
    @32
    wrex
    vd
    @19
    wrex
    #
    @59
    @78
    @15
    @31
    vd
    ve
    @19
    @32
    reeanv
    @59
    @82
    @63
    @61
    @18
    cres
    #
    @12
    cfv
    #
    cc0
    wceq
    #
    @61
    cn
    cres
    #
    @28
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    wa
    #
    vf
    @77
    wrex
    #
    @78
    @59
    @82
    @91
    @59
    @81
    @91
    vd
    ve
    @19
    @32
    @59
    @8
    @19
    wcel
    #
    @25
    @32
    wcel
    #
    wa
    #
    wa
    #
    @81
    @91
    @95
    @81
    wa
    #
    @8
    @25
    cun
    #
    @77
    wcel
    @7
    @97
    @9
    cres
    #
    wceq
    #
    @97
    @18
    cres
    #
    @12
    cfv
    #
    cc0
    wceq
    #
    @97
    cn
    cres
    #
    @28
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    wa
    #
    @91
    @96
    @97
    cn0
    @18
    cn
    cun
    #
    cmap
    co
    #
    @77
    @96
    @92
    @93
    @8
    @47
    cres
    #
    @25
    @47
    cres
    #
    wceq
    #
    @97
    @109
    wcel
    @59
    @92
    @93
    @81
    simplrl
    #
    @59
    @92
    @93
    @81
    simplrr
    #
    @96
    @110
    @10
    @111
    @5
    @110
    @10
    wceq
    @58
    @94
    @81
    @5
    @47
    @9
    @8
    @5
    @9
    @47
    @48
    eqcomd
    #
    reseq2d
    ad3antrrr
    @96
    @111
    @26
    @7
    @10
    @5
    @111
    @26
    wceq
    @58
    @94
    @81
    @5
    @47
    @9
    @25
    @115
    reseq2d
    ad3antrrr
    @95
    @15
    @27
    @30
    simprrl
    #
    @95
    @11
    @14
    @31
    simprll
    #
    3eqtr2d
    eqtr4d
    #
    @18
    cn
    cn0
    @8
    @25
    elmapresaun
    syl3anc
    @5
    @109
    @77
    wceq
    @58
    @94
    @81
    @5
    @108
    cz
    cn0
    cmap
    @5
    @108
    @18
    c1
    cuz
    cfv
    #
    cun
    #
    cz
    cn
    @119
    @18
    nnuz
    uneq2i
    @5
    @45
    @53
    c1
    @16
    cle
    wbr
    @120
    cz
    wceq
    @46
    @53
    @5
    1z
    a1i
    @5
    @16
    cN
    nn0p1nn
    nnge1d
    cN
    c1
    lzunuz
    syl3anc
    syl5eq
    oveq2d
    ad3antrrr
    eleqtrd
    @96
    @99
    @102
    @105
    @96
    @7
    @10
    @26
    cun
    #
    @98
    @96
    @7
    @7
    @7
    cun
    @121
    @7
    unidm
    @96
    @7
    @10
    @7
    @26
    @117
    @116
    uneq12d
    syl5eqr
    @8
    @25
    @9
    resundir
    syl6eqr
    @96
    @101
    @13
    cc0
    @96
    @100
    @8
    @12
    @96
    @100
    @25
    @8
    cun
    #
    @18
    cres
    #
    @8
    @97
    @122
    @18
    @8
    @25
    uncom
    reseq1i
    @96
    @93
    @92
    @25
    cn
    @18
    cin
    #
    cres
    #
    @8
    @124
    cres
    #
    wceq
    @123
    @8
    wceq
    @114
    @113
    @96
    @125
    @26
    @126
    @5
    @125
    @26
    wceq
    @58
    @94
    @81
    @5
    @124
    @9
    @25
    @5
    @124
    @47
    @9
    cn
    @18
    incom
    @115
    syl5eq
    #
    reseq2d
    ad3antrrr
    @96
    @126
    @10
    @7
    @26
    @5
    @126
    @10
    wceq
    @58
    @94
    @81
    @5
    @124
    @9
    @8
    @127
    reseq2d
    ad3antrrr
    @117
    @116
    3eqtr2d
    eqtr4d
    cn
    @18
    cn0
    @25
    @8
    elmapresaunres2
    syl3anc
    syl5eq
    fveq2d
    @95
    @11
    @14
    @31
    simprlr
    eqtrd
    @96
    @104
    @29
    cc0
    @96
    @103
    @25
    @28
    @96
    @92
    @93
    @112
    @103
    @25
    wceq
    @113
    @114
    @118
    @18
    cn
    cn0
    @8
    @25
    elmapresaunres2
    syl3anc
    fveq2d
    @95
    @15
    @27
    @30
    simprrr
    eqtrd
    jca32
    @90
    @107
    vf
    @97
    @77
    @61
    @97
    wceq
    #
    @63
    @99
    @89
    @106
    @128
    @62
    @98
    @7
    @61
    @97
    @9
    reseq1
    eqeq2d
    @128
    @85
    @102
    @88
    @105
    @128
    @84
    @101
    cc0
    @128
    @83
    @100
    @12
    @61
    @97
    @18
    reseq1
    fveq2d
    eqeq1d
    @128
    @87
    @104
    cc0
    @128
    @86
    @103
    @28
    @61
    @97
    cn
    reseq1
    fveq2d
    eqeq1d
    anbi12d
    anbi12d
    rspcev
    syl2anc
    ex
    rexlimdvva
    @59
    @90
    @82
    vf
    @77
    @59
    @61
    @77
    wcel
    #
    wa
    #
    @90
    @82
    @130
    @90
    wa
    #
    @83
    @19
    wcel
    #
    @86
    @32
    wcel
    #
    @7
    @83
    @9
    cres
    #
    wceq
    #
    @85
    wa
    #
    @7
    @86
    @9
    cres
    #
    wceq
    #
    @88
    wa
    #
    wa
    #
    @82
    @130
    @132
    @90
    @130
    @129
    @18
    cz
    wss
    #
    @132
    @59
    @129
    simpr
    #
    cz
    @17
    difss
    #
    @61
    cn0
    cz
    @18
    elmapssres
    sylancl
    adantr
    @130
    @133
    @90
    @130
    @129
    cn
    cz
    wss
    #
    @133
    @142
    nnssz
    @61
    cn0
    cz
    cn
    elmapssres
    sylancl
    adantr
    @131
    @136
    @138
    @88
    @131
    @135
    @85
    @131
    @7
    @62
    @134
    @130
    @63
    @89
    simprl
    #
    @131
    @61
    @9
    @18
    @5
    @41
    @58
    @129
    @90
    @49
    ad3antrrr
    resabs1d
    eqtr4d
    @130
    @63
    @85
    @88
    simprrl
    jca
    @131
    @7
    @62
    @137
    @145
    @52
    @137
    @62
    wceq
    @131
    @54
    @61
    @9
    cn
    resabs1
    mp1i
    eqtr4d
    @130
    @63
    @85
    @88
    simprrr
    jca32
    @81
    @140
    @136
    @31
    wa
    vd
    ve
    @83
    @86
    @19
    @32
    @8
    @83
    wceq
    #
    @15
    @136
    @31
    @146
    @11
    @135
    @14
    @85
    @146
    @10
    @134
    @7
    @8
    @83
    @9
    reseq1
    eqeq2d
    @146
    @13
    @84
    cc0
    @8
    @83
    @12
    fveq2
    eqeq1d
    anbi12d
    anbi1d
    @25
    @86
    wceq
    #
    @31
    @139
    @136
    @147
    @27
    @138
    @30
    @88
    @147
    @26
    @137
    @7
    @25
    @86
    @9
    reseq1
    eqeq2d
    @147
    @29
    @87
    cc0
    @25
    @86
    @28
    fveq2
    eqeq1d
    anbi12d
    anbi2d
    rspc2ev
    syl3anc
    ex
    rexlimdva
    impbid
    @59
    @90
    @76
    vf
    @77
    @130
    @89
    @75
    @63
    @130
    @89
    @84
    c2
    cexp
    co
    #
    @87
    c2
    cexp
    co
    #
    caddc
    co
    #
    cc0
    wceq
    #
    @75
    @130
    @84
    cr
    wcel
    @87
    cr
    wcel
    @89
    @151
    wb
    @130
    @84
    @130
    cz
    @18
    cmap
    co
    #
    cz
    @83
    @12
    @130
    @56
    @152
    cz
    @12
    wf
    @5
    @56
    @57
    @129
    simplrl
    @12
    @18
    mzpf
    syl
    @129
    @83
    @152
    wcel
    #
    @59
    @129
    @61
    @64
    wcel
    #
    @141
    @153
    @77
    @64
    @61
    @43
    cn0
    cz
    wss
    @77
    @64
    wss
    zex
    nn0ssz
    cn0
    cz
    cz
    cvv
    mapss
    mp2an
    sseli
    #
    @143
    @61
    cz
    cz
    @18
    elmapssres
    sylancl
    adantl
    ffvelrnd
    zred
    @130
    @87
    @130
    cz
    cn
    cmap
    co
    #
    cz
    @86
    @28
    @130
    @57
    @156
    cz
    @28
    wf
    @5
    @56
    @57
    @129
    simplrr
    @28
    cn
    mzpf
    syl
    @129
    @86
    @156
    wcel
    #
    @59
    @129
    @154
    @144
    @157
    @155
    nnssz
    @61
    cz
    cz
    cn
    elmapssres
    sylancl
    adantl
    ffvelrnd
    zred
    @84
    @87
    sumsqeq0
    syl2anc
    @130
    @74
    @150
    cc0
    @130
    @154
    @74
    @150
    wceq
    @129
    @154
    @59
    @155
    adantl
    vg
    @61
    @72
    @150
    @64
    @73
    @65
    @61
    wceq
    #
    @68
    @148
    @71
    @149
    caddc
    @158
    @67
    @84
    c2
    cexp
    @158
    @66
    @83
    @12
    @65
    @61
    @18
    reseq1
    fveq2d
    oveq1d
    @158
    @70
    @87
    c2
    cexp
    @158
    @69
    @86
    @28
    @65
    @61
    cn
    reseq1
    fveq2d
    oveq1d
    oveq12d
    @73
    eqid
    @148
    @149
    caddc
    ovex
    fvmpt
    syl
    eqeq1d
    bitr4d
    anbi2d
    rexbidva
    bitrd
    syl5bbr
    abbidv
    syl5eq
    @59
    @5
    @43
    @9
    cz
    wss
    #
    wa
    #
    @73
    cz
    cmzp
    cfv
    #
    wcel
    #
    @79
    @0
    wcel
    @5
    @58
    simpl
    @160
    @59
    @43
    @159
    zex
    @9
    @119
    cz
    c1
    cN
    fzssuz
    c1
    uzssz
    sstri
    pm3.2i
    a1i
    @59
    vg
    @64
    @68
    cmpt
    @161
    wcel
    #
    vg
    @64
    @71
    cmpt
    @161
    wcel
    #
    @162
    @59
    vg
    @64
    @67
    cmpt
    @161
    wcel
    #
    c2
    cn0
    wcel
    #
    @163
    @59
    @43
    @141
    @56
    @165
    @43
    @59
    zex
    a1i
    #
    @141
    @59
    @143
    a1i
    @5
    @56
    @57
    simprl
    vg
    @12
    @18
    cz
    mzpresrename
    syl3anc
    2nn0
    vg
    @67
    c2
    cz
    mzpexpmpt
    sylancl
    @59
    vg
    @64
    @70
    cmpt
    @161
    wcel
    #
    @166
    @164
    @59
    @43
    @144
    @57
    @168
    @167
    @144
    @59
    nnssz
    a1i
    @5
    @56
    @57
    simprr
    vg
    @28
    cn
    cz
    mzpresrename
    syl3anc
    2nn0
    vg
    @70
    c2
    cz
    mzpexpmpt
    sylancl
    vg
    @68
    @71
    cz
    mzpaddmpt
    syl2anc
    vf
    vc
    @73
    cz
    cN
    eldioph2
    syl3anc
    eqeltrd
    @55
    @3
    @60
    @0
    cA
    @21
    cB
    @34
    ineq12
    eleq1d
    syl5ibrcom
    rexlimdvva
    syl5bir
    sylbid
    syl
    anabsi5
end
