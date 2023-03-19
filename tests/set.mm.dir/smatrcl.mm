include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cxp.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "cdm.mm"
include "wfun.mm"
include "cn.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cif.mm"
include "cop.mm"
include "cmpt2.mm"
include "ccom.mm"
include "elmapi.mm"
include "ffun.mm"
include "3syl.mm"
include "eqid.mm"
include "mpt2fun.mm"
include "a1i.mm"
include "funco.mm"
include "syl2anc.mm"
include "csmat.mm"
include "cfv.mm"
include "wceq.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "smatfval.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "funeqd.mm"
include "mpbird.mm"
include "fdmrn.mm"
include "sylib.mm"
include "dmeqd.mm"
include "ccnv.mm"
include "cima.mm"
include "dmco.mm"
include "wa.mm"
include "fdm.mm"
include "imaeq2d.mm"
include "eleq2d.mm"
include "wb.mm"
include "wfn.mm"
include "opex.mm"
include "fnmpt2i.mm"
include "elpreima.mm"
include "ax-mp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cle.mm"
include "simplr.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "breq1.mm"
include "id.mm"
include "oveq1.mm"
include "ifbieq12d.mm"
include "opeq1d.mm"
include "opeq2d.mm"
include "ovmpt2.mm"
include "adantl.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "wn.mm"
include "wo.mm"
include "ifel.mm"
include "simplrl.mm"
include "nnred.mm"
include "cr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "ltled.mm"
include "elfzle2.mm"
include "syl.mm"
include "letrd.mm"
include "jca.mm"
include "cz.mm"
include "nnzd.mm"
include "fznn.mm"
include "ltletrd.mm"
include "nnltlem1.mm"
include "mpbid.mm"
include "2thd.mm"
include "pm5.32da.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "peano2nnd.mm"
include "biantrurd.mm"
include "zltp1le.mm"
include "zltlem1.mm"
include "bitr3d.mm"
include "3bitr2d.mm"
include "anbi2d.mm"
include "orbi12d.mm"
include "pm4.42.mm"
include "ancom.mm"
include "orbi12i.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "syl5bb.mm"
include "simplrr.mm"
include "simprr.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "an4.mm"
include "adantr.mm"
include "bitr4d.mm"
include "elxp6.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitr4g.mm"
include "3bitrd.mm"
include "eqrdv.mm"
include "feq2d.mm"
include "rneqd.mm"
include "rncoss.mm"
include "syl6eqss.mm"
include "frn.mm"
include "sstrd.mm"
include "fss.mm"
include "cvv.mm"
include "reldmmap.mm"
include "ovrcl.mm"
include "simpld.mm"
include "ovex.mm"
include "xpex.mm"
include "elmapg.mm"
include "sylancl.mm"

theorem smatrcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let cV: class V
  let vx: setvar x
  assume smat.s: |- S = ( K ( subMat1 ` A ) L )
  assume smat.m: |- ( ph -> M e. NN )
  assume smat.n: |- ( ph -> N e. NN )
  assume smat.k: |- ( ph -> K e. ( 1 ... M ) )
  assume smat.l: |- ( ph -> L e. ( 1 ... N ) )
  assume smat.a: |- ( ph -> A e. ( B ^m ( ( 1 ... M ) X. ( 1 ... N ) ) ) )


  assert |- ( ph -> S e. ( B ^m ( ( 1 ... ( M - 1 ) ) X. ( 1 ... ( N - 1 ) ) ) ) )

  proof
    wph
    cS
    cB
    c1
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cxp
    #
    cmap
    co
    wcel
    #
    @4
    cB
    cS
    wf
    #
    wph
    @4
    cS
    crn
    #
    cS
    wf
    #
    @7
    cB
    wss
    @6
    wph
    cS
    cdm
    #
    @7
    cS
    wf
    #
    @8
    wph
    cS
    wfun
    #
    @10
    wph
    @11
    cA
    vi
    vj
    cn
    cn
    vi
    cv
    #
    cK
    clt
    wbr
    #
    @12
    @12
    c1
    caddc
    co
    #
    cif
    #
    vj
    cv
    #
    cL
    clt
    wbr
    #
    @16
    @16
    c1
    caddc
    co
    #
    cif
    #
    cop
    #
    cmpt2
    #
    ccom
    #
    wfun
    #
    wph
    cA
    wfun
    #
    @21
    wfun
    #
    @23
    wph
    cA
    cB
    c1
    cM
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    cxp
    #
    cmap
    co
    #
    wcel
    #
    @28
    cB
    cA
    wf
    #
    @24
    smat.a
    cA
    cB
    @28
    elmapi
    #
    @28
    cB
    cA
    ffun
    3syl
    @25
    wph
    vi
    vj
    cn
    cn
    @20
    @21
    @21
    eqid
    #
    mpt2fun
    a1i
    cA
    @21
    funco
    syl2anc
    wph
    cS
    @22
    wph
    cS
    cK
    cL
    cA
    csmat
    cfv
    co
    #
    @22
    smat.s
    wph
    cK
    cn
    wcel
    cL
    cn
    wcel
    @30
    @34
    @22
    wceq
    wph
    @26
    cn
    cK
    cM
    fz1ssnn
    smat.k
    sseldi
    #
    wph
    @27
    cn
    cL
    cN
    fz1ssnn
    smat.l
    sseldi
    #
    smat.a
    vi
    vj
    cK
    cL
    cA
    @29
    smatfval
    syl3anc
    syl5eq
    #
    funeqd
    mpbird
    cS
    fdmrn
    sylib
    wph
    @9
    @4
    @7
    cS
    wph
    @9
    @22
    cdm
    #
    @4
    wph
    cS
    @22
    @37
    dmeqd
    wph
    @38
    @21
    ccnv
    #
    cA
    cdm
    #
    cima
    #
    @4
    cA
    @21
    dmco
    wph
    vx
    @41
    @4
    wph
    vx
    cv
    #
    @41
    wcel
    @42
    @39
    @28
    cima
    #
    wcel
    #
    @42
    cn
    cn
    cxp
    #
    wcel
    #
    @42
    @21
    cfv
    #
    @28
    wcel
    #
    wa
    #
    @42
    @4
    wcel
    #
    wph
    @41
    @43
    @42
    wph
    @40
    @28
    @39
    wph
    @30
    @31
    @40
    @28
    wceq
    smat.a
    @32
    @28
    cB
    cA
    fdm
    3syl
    imaeq2d
    eleq2d
    @44
    @49
    wb
    #
    wph
    @21
    @45
    wfn
    @51
    vi
    vj
    cn
    cn
    @20
    @21
    @33
    @15
    @19
    opex
    fnmpt2i
    @45
    @42
    @28
    @21
    elpreima
    ax-mp
    a1i
    wph
    @42
    @42
    c1st
    cfv
    #
    @42
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @52
    cn
    wcel
    #
    @53
    cn
    wcel
    #
    wa
    #
    @48
    wa
    #
    wa
    #
    @55
    @52
    @1
    wcel
    #
    @53
    @3
    wcel
    #
    wa
    #
    wa
    @49
    @50
    wph
    @55
    @59
    @63
    wph
    @55
    wa
    #
    @59
    @58
    @52
    @0
    cle
    wbr
    #
    @53
    @2
    cle
    wbr
    #
    wa
    #
    wa
    #
    @63
    @64
    @58
    @48
    @67
    @64
    @58
    wa
    #
    @48
    @52
    cK
    clt
    wbr
    #
    @52
    @52
    c1
    caddc
    co
    #
    cif
    #
    @26
    wcel
    #
    @53
    cL
    clt
    wbr
    #
    @53
    @53
    c1
    caddc
    co
    #
    cif
    #
    @27
    wcel
    #
    wa
    #
    @67
    @69
    @48
    @72
    @76
    cop
    #
    @28
    wcel
    @78
    @69
    @47
    @79
    @28
    @69
    @47
    @52
    @53
    @21
    co
    #
    @79
    @69
    @47
    @54
    @21
    cfv
    @80
    @69
    @42
    @54
    @21
    wph
    @55
    @58
    simplr
    fveq2d
    @52
    @53
    @21
    df-ov
    syl6eqr
    @58
    @80
    @79
    wceq
    @64
    vi
    vj
    @52
    @53
    cn
    cn
    @20
    @79
    @21
    @72
    @19
    cop
    @12
    @52
    wceq
    #
    @15
    @72
    @19
    @81
    @13
    @70
    @12
    @14
    @52
    @71
    @12
    @52
    cK
    clt
    breq1
    @81
    id
    @12
    @52
    c1
    caddc
    oveq1
    ifbieq12d
    opeq1d
    @16
    @53
    wceq
    #
    @19
    @76
    @72
    @82
    @17
    @74
    @16
    @18
    @53
    @75
    @16
    @53
    cL
    clt
    breq1
    @82
    id
    @16
    @53
    c1
    caddc
    oveq1
    ifbieq12d
    opeq2d
    @33
    @72
    @76
    opex
    ovmpt2
    adantl
    eqtrd
    eleq1d
    @72
    @76
    @26
    @27
    opelxp
    syl6bb
    @69
    @73
    @65
    @77
    @66
    @73
    @70
    @52
    @26
    wcel
    #
    wa
    #
    @70
    wn
    #
    @71
    @26
    wcel
    #
    wa
    #
    wo
    #
    @69
    @65
    @70
    @52
    @71
    @26
    ifel
    @69
    @88
    @70
    @65
    wa
    #
    @85
    @65
    wa
    #
    wo
    #
    @65
    @69
    @84
    @89
    @87
    @90
    @69
    @70
    @83
    @65
    @69
    @70
    wa
    #
    @83
    @65
    @92
    @83
    @56
    @52
    cM
    cle
    wbr
    #
    wa
    #
    @92
    @56
    @93
    @64
    @56
    @57
    @70
    simplrl
    #
    @92
    @52
    cK
    cM
    @92
    @52
    @95
    nnred
    #
    wph
    cK
    cr
    wcel
    @55
    @58
    @70
    wph
    cK
    @35
    nnred
    ad3antrrr
    #
    wph
    cM
    cr
    wcel
    @55
    @58
    @70
    wph
    cM
    smat.m
    nnred
    ad3antrrr
    #
    @92
    @52
    cK
    @96
    @97
    @69
    @70
    simpr
    #
    ltled
    wph
    cK
    cM
    cle
    wbr
    #
    @55
    @58
    @70
    wph
    cK
    @26
    wcel
    @100
    smat.k
    cK
    c1
    cM
    elfzle2
    syl
    ad3antrrr
    #
    letrd
    jca
    wph
    @83
    @94
    wb
    #
    @55
    @58
    @70
    wph
    cM
    cz
    wcel
    #
    @102
    wph
    cM
    smat.m
    nnzd
    #
    @52
    cM
    fznn
    syl
    ad3antrrr
    mpbird
    @92
    @52
    cM
    clt
    wbr
    #
    @65
    @92
    @52
    cK
    cM
    @96
    @97
    @98
    @99
    @101
    ltletrd
    @92
    @56
    cM
    cn
    wcel
    #
    @105
    @65
    wb
    @95
    wph
    @106
    @55
    @58
    @70
    smat.m
    ad3antrrr
    @52
    cM
    nnltlem1
    syl2anc
    mpbid
    2thd
    pm5.32da
    @69
    @86
    @65
    @85
    @69
    @86
    @71
    cn
    wcel
    #
    @71
    cM
    cle
    wbr
    #
    wa
    #
    @108
    @65
    wph
    @86
    @109
    wb
    #
    @55
    @58
    wph
    @103
    @110
    @104
    @71
    cM
    fznn
    syl
    ad2antrr
    @69
    @107
    @108
    @69
    @52
    @64
    @56
    @57
    simprl
    #
    peano2nnd
    biantrurd
    @69
    @52
    cz
    wcel
    #
    @103
    @108
    @65
    wb
    @69
    @52
    @111
    nnzd
    wph
    @103
    @55
    @58
    @104
    ad2antrr
    @112
    @103
    wa
    @105
    @108
    @65
    @52
    cM
    zltp1le
    @52
    cM
    zltlem1
    bitr3d
    syl2anc
    3bitr2d
    anbi2d
    orbi12d
    @65
    @65
    @70
    wa
    #
    @65
    @85
    wa
    #
    wo
    @91
    @65
    @70
    pm4.42
    @113
    @89
    @114
    @90
    @65
    @70
    ancom
    @65
    @85
    ancom
    orbi12i
    bitri
    syl6bbr
    syl5bb
    @77
    @74
    @53
    @27
    wcel
    #
    wa
    #
    @74
    wn
    #
    @75
    @27
    wcel
    #
    wa
    #
    wo
    #
    @69
    @66
    @74
    @53
    @75
    @27
    ifel
    @69
    @120
    @74
    @66
    wa
    #
    @117
    @66
    wa
    #
    wo
    #
    @66
    @69
    @116
    @121
    @119
    @122
    @69
    @74
    @115
    @66
    @69
    @74
    wa
    #
    @115
    @66
    @124
    @115
    @57
    @53
    cN
    cle
    wbr
    #
    wa
    #
    @124
    @57
    @125
    @64
    @56
    @57
    @74
    simplrr
    #
    @124
    @53
    cL
    cN
    @124
    @53
    @127
    nnred
    #
    wph
    cL
    cr
    wcel
    @55
    @58
    @74
    wph
    cL
    @36
    nnred
    ad3antrrr
    #
    wph
    cN
    cr
    wcel
    @55
    @58
    @74
    wph
    cN
    smat.n
    nnred
    ad3antrrr
    #
    @124
    @53
    cL
    @128
    @129
    @69
    @74
    simpr
    #
    ltled
    wph
    cL
    cN
    cle
    wbr
    #
    @55
    @58
    @74
    wph
    cL
    @27
    wcel
    @132
    smat.l
    cL
    c1
    cN
    elfzle2
    syl
    ad3antrrr
    #
    letrd
    jca
    wph
    @115
    @126
    wb
    #
    @55
    @58
    @74
    wph
    cN
    cz
    wcel
    #
    @134
    wph
    cN
    smat.n
    nnzd
    #
    @53
    cN
    fznn
    syl
    ad3antrrr
    mpbird
    @124
    @53
    cN
    clt
    wbr
    #
    @66
    @124
    @53
    cL
    cN
    @128
    @129
    @130
    @131
    @133
    ltletrd
    @124
    @57
    cN
    cn
    wcel
    #
    @137
    @66
    wb
    @127
    wph
    @138
    @55
    @58
    @74
    smat.n
    ad3antrrr
    @53
    cN
    nnltlem1
    syl2anc
    mpbid
    2thd
    pm5.32da
    @69
    @118
    @66
    @117
    @69
    @118
    @75
    cn
    wcel
    #
    @75
    cN
    cle
    wbr
    #
    wa
    #
    @140
    @66
    wph
    @118
    @141
    wb
    #
    @55
    @58
    wph
    @135
    @142
    @136
    @75
    cN
    fznn
    syl
    ad2antrr
    @69
    @139
    @140
    @69
    @53
    @64
    @56
    @57
    simprr
    #
    peano2nnd
    biantrurd
    @69
    @53
    cz
    wcel
    #
    @135
    @140
    @66
    wb
    @69
    @53
    @143
    nnzd
    wph
    @135
    @55
    @58
    @136
    ad2antrr
    @144
    @135
    wa
    @137
    @140
    @66
    @53
    cN
    zltp1le
    @53
    cN
    zltlem1
    bitr3d
    syl2anc
    3bitr2d
    anbi2d
    orbi12d
    @66
    @66
    @74
    wa
    #
    @66
    @117
    wa
    #
    wo
    @123
    @66
    @74
    pm4.42
    @145
    @121
    @146
    @122
    @66
    @74
    ancom
    @66
    @117
    ancom
    orbi12i
    bitri
    syl6bbr
    syl5bb
    anbi12d
    bitrd
    pm5.32da
    wph
    @63
    @68
    wb
    @55
    wph
    @63
    @56
    @65
    wa
    #
    @57
    @66
    wa
    #
    wa
    @68
    wph
    @61
    @147
    @62
    @148
    wph
    @0
    cz
    wcel
    @61
    @147
    wb
    wph
    cM
    c1
    @104
    wph
    1zzd
    #
    zsubcld
    @52
    @0
    fznn
    syl
    wph
    @2
    cz
    wcel
    @62
    @148
    wb
    wph
    cN
    c1
    @136
    @149
    zsubcld
    @53
    @2
    fznn
    syl
    anbi12d
    @56
    @65
    @57
    @66
    an4
    syl6bb
    adantr
    bitr4d
    pm5.32da
    @49
    @55
    @58
    wa
    #
    @48
    wa
    @60
    @46
    @150
    @48
    @42
    cn
    cn
    elxp6
    anbi1i
    @55
    @58
    @48
    anass
    bitri
    @42
    @1
    @3
    elxp6
    3bitr4g
    3bitrd
    eqrdv
    syl5eq
    eqtrd
    feq2d
    mpbid
    wph
    @7
    cA
    crn
    #
    cB
    wph
    @7
    @22
    crn
    @151
    wph
    cS
    @22
    @37
    rneqd
    cA
    @21
    rncoss
    syl6eqss
    wph
    @30
    @31
    @151
    cB
    wss
    smat.a
    @32
    @28
    cB
    cA
    frn
    3syl
    sstrd
    @4
    @7
    cB
    cS
    fss
    syl2anc
    wph
    cB
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @5
    @6
    wb
    wph
    @152
    @28
    cvv
    wcel
    #
    wph
    @30
    @152
    @153
    wa
    smat.a
    cB
    @28
    cA
    cmap
    reldmmap
    ovrcl
    syl
    simpld
    @1
    @3
    c1
    @0
    cfz
    ovex
    c1
    @2
    cfz
    ovex
    xpex
    cB
    @4
    cS
    cvv
    cvv
    elmapg
    sylancl
    mpbird
end
