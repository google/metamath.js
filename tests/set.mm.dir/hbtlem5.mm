include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cdg1.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "wrex.mm"
include "cmnf.mm"
include "csn.mm"
include "cun.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "lidlss.mm"
include "syl.mm"
include "sselda.mm"
include "deg1cl.mm"
include "wo.mm"
include "elun.mm"
include "cn.mm"
include "nnssnn0.mm"
include "cr.mm"
include "nn0re.mm"
include "arch.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "wceq.mm"
include "elsni.mm"
include "cc0.mm"
include "0nn0.mm"
include "mnflt0.mm"
include "breq2.mm"
include "rspcev.mm"
include "mp2an.mm"
include "breq1.mm"
include "rexbidv.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "sylbi.mm"
include "wi.mm"
include "wral.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "imbi2d.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "c0g.mm"
include "crg.mm"
include "wb.mm"
include "adantr.mm"
include "deg1lt0.mm"
include "syl2anc.mm"
include "ply1ring.mm"
include "lidl0cl.mm"
include "eleq1a.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "w3a.mm"
include "cle.mm"
include "cz.mm"
include "3ad2ant2.mm"
include "simpl1.mm"
include "nn0zd.mm"
include "degltp1le.mm"
include "cco1.mm"
include "cab.mm"
include "sseq12d.mm"
include "rspcva.mm"
include "sylan2.mm"
include "adantl.mm"
include "simpl.mm"
include "hbtlem1.mm"
include "syl3anc.mm"
include "3sstr3d.mm"
include "3adant3.mm"
include "simpr.mm"
include "eqidd.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "elab.mm"
include "sylibr.mm"
include "sseldd.mm"
include "csg.mm"
include "cplusg.mm"
include "cgrp.mm"
include "simpll2.mm"
include "ringgrp.mm"
include "simplrl.mm"
include "simprl.mm"
include "grpnpcan.mm"
include "ad2antrr.mm"
include "simpll1.mm"
include "simplrr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "deg1sublt.mm"
include "lidlsubcl.mm"
include "syl22anc.mm"
include "simpll3.mm"
include "mpd.mm"
include "lidlacl.mm"
include "eqeltrrd.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "expr.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "rsp.mm"
include "syl6com.mm"
include "com23.mm"
include "imp.mm"
include "rexlimdv.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem hbtlem5
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  assume hbtlem.p: |- P = ( Poly1 ` R )
  assume hbtlem.u: |- U = ( LIdeal ` P )
  assume hbtlem.s: |- S = ( ldgIdlSeq ` R )
  assume hbtlem3.r: |- ( ph -> R e. Ring )
  assume hbtlem3.i: |- ( ph -> I e. U )
  assume hbtlem3.j: |- ( ph -> J e. U )
  assume hbtlem3.ij: |- ( ph -> I C_ J )
  assume hbtlem5.e: |- ( ph -> A. x e. NN0 ( ( S ` J ) ` x ) C_ ( ( S ` I ) ` x ) )

  disjoint I x
  disjoint J x
  disjoint S x
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I d
  disjoint I e
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint J e
  disjoint P a
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint b x
  assert |- ( ph -> I = J )

  proof
    wph
    cI
    cJ
    hbtlem3.ij
    wph
    va
    cJ
    cI
    wph
    va
    cv
    #
    cJ
    wcel
    #
    @0
    cI
    wcel
    #
    wph
    @1
    wa
    #
    @0
    cR
    cdg1
    cfv
    #
    cfv
    #
    vb
    cv
    #
    clt
    wbr
    #
    vb
    cn0
    wrex
    #
    @2
    @3
    @5
    cn0
    cmnf
    csn
    #
    cun
    #
    wcel
    #
    @8
    @3
    @0
    cP
    cbs
    cfv
    #
    wcel
    #
    @11
    wph
    cJ
    @12
    @0
    wph
    cJ
    cU
    wcel
    #
    cJ
    @12
    wss
    #
    hbtlem3.j
    @12
    cJ
    cU
    cP
    @12
    eqid
    #
    hbtlem.u
    lidlss
    syl
    #
    sselda
    #
    @12
    @4
    cP
    cR
    @0
    @4
    eqid
    #
    hbtlem.p
    @16
    deg1cl
    syl
    @11
    @5
    cn0
    wcel
    #
    @5
    @9
    wcel
    #
    wo
    @8
    @5
    cn0
    @9
    elun
    @20
    @8
    @21
    cn
    cn0
    wss
    @20
    @7
    vb
    cn
    wrex
    #
    @8
    nnssnn0
    @20
    @5
    cr
    wcel
    @22
    @5
    nn0re
    @5
    vb
    arch
    syl
    @7
    vb
    cn
    cn0
    ssrexv
    mpsyl
    @21
    @5
    cmnf
    wceq
    #
    @8
    @5
    cmnf
    elsni
    @23
    @8
    cmnf
    @6
    clt
    wbr
    #
    vb
    cn0
    wrex
    #
    cc0
    cn0
    wcel
    cmnf
    cc0
    clt
    wbr
    #
    @25
    0nn0
    mnflt0
    @24
    @26
    vb
    cc0
    cn0
    @6
    cc0
    cmnf
    clt
    breq2
    rspcev
    mp2an
    @23
    @7
    @24
    vb
    cn0
    @5
    cmnf
    @6
    clt
    breq1
    rexbidv
    mpbiri
    syl
    jaoi
    sylbi
    syl
    @3
    @7
    @2
    vb
    cn0
    wph
    @1
    @6
    cn0
    wcel
    #
    @7
    @2
    wi
    #
    wi
    wph
    @27
    @1
    @28
    @27
    wph
    @28
    va
    cJ
    wral
    #
    @1
    @28
    wi
    wph
    @5
    vc
    cv
    #
    clt
    wbr
    #
    @2
    wi
    #
    va
    cJ
    wral
    #
    wi
    wph
    @5
    cc0
    clt
    wbr
    #
    @2
    wi
    #
    va
    cJ
    wral
    #
    wi
    wph
    @29
    wi
    #
    wph
    vd
    cv
    #
    @4
    cfv
    #
    @6
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @38
    cI
    wcel
    #
    wi
    #
    vd
    cJ
    wral
    #
    wi
    @37
    vc
    vb
    @6
    @30
    cc0
    wceq
    #
    @33
    @36
    wph
    @45
    @32
    @35
    va
    cJ
    @45
    @31
    @34
    @2
    @30
    cc0
    @5
    clt
    breq2
    imbi1d
    ralbidv
    imbi2d
    vc
    vb
    weq
    #
    @33
    @29
    wph
    @46
    @32
    @28
    va
    cJ
    @46
    @31
    @7
    @2
    @30
    @6
    @5
    clt
    breq2
    imbi1d
    ralbidv
    imbi2d
    #
    @30
    @40
    wceq
    #
    @33
    @44
    wph
    @48
    @33
    @5
    @40
    clt
    wbr
    #
    @2
    wi
    #
    va
    cJ
    wral
    @44
    @48
    @32
    @50
    va
    cJ
    @48
    @31
    @49
    @2
    @30
    @40
    @5
    clt
    breq2
    imbi1d
    ralbidv
    @50
    @43
    va
    vd
    cJ
    va
    vd
    weq
    #
    @49
    @41
    @2
    @42
    @51
    @5
    @39
    @40
    clt
    @0
    @38
    @4
    fveq2
    breq1d
    @0
    @38
    cI
    eleq1
    imbi12d
    cbvralv
    syl6bb
    imbi2d
    @47
    wph
    @35
    va
    cJ
    @3
    @34
    @0
    cP
    c0g
    cfv
    #
    wceq
    #
    @2
    @3
    cR
    crg
    wcel
    #
    @13
    @34
    @53
    wb
    wph
    @54
    @1
    hbtlem3.r
    adantr
    @18
    @12
    @4
    cP
    cR
    @0
    @52
    @19
    hbtlem.p
    @52
    eqid
    #
    @16
    deg1lt0
    syl2anc
    wph
    @53
    @2
    wi
    #
    @1
    wph
    @52
    cI
    wcel
    #
    @56
    wph
    cP
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    @57
    wph
    @54
    @58
    hbtlem3.r
    cP
    cR
    hbtlem.p
    ply1ring
    syl
    #
    hbtlem3.i
    cP
    cU
    cI
    @52
    hbtlem.u
    @55
    lidl0cl
    syl2anc
    @52
    cI
    @0
    eleq1a
    syl
    adantr
    sylbid
    ralrimiva
    @27
    wph
    @29
    @44
    @27
    wph
    @29
    @44
    @27
    wph
    @29
    w3a
    #
    @43
    vd
    cJ
    @61
    @38
    cJ
    wcel
    #
    wa
    #
    @41
    @39
    @6
    cle
    wbr
    #
    @42
    @63
    @39
    @10
    wcel
    #
    @6
    cz
    wcel
    @41
    @64
    wb
    @63
    @38
    @12
    wcel
    #
    @65
    @61
    cJ
    @12
    @38
    wph
    @27
    @15
    @29
    @17
    3ad2ant2
    sselda
    @12
    @4
    cP
    cR
    @38
    @19
    hbtlem.p
    @16
    deg1cl
    syl
    @63
    @6
    @27
    wph
    @29
    @62
    simpl1
    nn0zd
    @39
    @6
    degltp1le
    syl2anc
    @61
    @62
    @64
    @42
    @61
    @62
    @64
    wa
    #
    wa
    #
    @6
    @38
    cco1
    cfv
    #
    cfv
    #
    ve
    cv
    #
    @4
    cfv
    #
    @6
    cle
    wbr
    #
    @30
    @6
    @71
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    ve
    cI
    wrex
    #
    vc
    cab
    #
    wcel
    #
    @42
    @68
    @77
    ve
    cJ
    wrex
    #
    vc
    cab
    #
    @79
    @70
    @61
    @82
    @79
    wss
    #
    @67
    @27
    wph
    @83
    @29
    @27
    wph
    wa
    #
    @6
    cJ
    cS
    cfv
    #
    cfv
    #
    @6
    cI
    cS
    cfv
    #
    cfv
    #
    @82
    @79
    wph
    @27
    vx
    cv
    #
    @85
    cfv
    #
    @89
    @87
    cfv
    #
    wss
    #
    vx
    cn0
    wral
    @86
    @88
    wss
    #
    hbtlem5.e
    @92
    @93
    vx
    @6
    cn0
    vx
    vb
    weq
    @90
    @86
    @91
    @88
    @89
    @6
    @85
    fveq2
    @89
    @6
    @87
    fveq2
    sseq12d
    rspcva
    sylan2
    @84
    @54
    @14
    @27
    @86
    @82
    wceq
    wph
    @54
    @27
    hbtlem3.r
    adantl
    #
    wph
    @14
    @27
    hbtlem3.j
    adantl
    @27
    wph
    simpl
    #
    @4
    cP
    cR
    cS
    cU
    vc
    ve
    cJ
    crg
    @6
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @19
    hbtlem1
    syl3anc
    @84
    @54
    @59
    @27
    @88
    @79
    wceq
    @94
    wph
    @59
    @27
    hbtlem3.i
    adantl
    @95
    @4
    cP
    cR
    cS
    cU
    vc
    ve
    cI
    crg
    @6
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @19
    hbtlem1
    syl3anc
    3sstr3d
    3adant3
    adantr
    @67
    @70
    @82
    wcel
    #
    @61
    @67
    @73
    @70
    @75
    wceq
    #
    wa
    #
    ve
    cJ
    wrex
    #
    @96
    @67
    @62
    @64
    @70
    @70
    wceq
    #
    @99
    @62
    @64
    simpl
    @62
    @64
    simpr
    @67
    @70
    eqidd
    @98
    @64
    @100
    wa
    ve
    @38
    cJ
    ve
    vd
    weq
    #
    @73
    @64
    @97
    @100
    @101
    @72
    @39
    @6
    cle
    @71
    @38
    @4
    fveq2
    breq1d
    @101
    @75
    @70
    @70
    @101
    @6
    @74
    @69
    @71
    @38
    cco1
    fveq2
    fveq1d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @81
    @99
    vc
    @70
    @6
    @69
    fvex
    #
    @30
    @70
    wceq
    #
    @77
    @98
    ve
    cJ
    @103
    @76
    @97
    @73
    @30
    @70
    @75
    eqeq1
    anbi2d
    #
    rexbidv
    elab
    sylibr
    adantl
    sseldd
    @80
    @98
    ve
    cI
    wrex
    #
    @68
    @42
    @78
    @105
    vc
    @70
    @102
    @103
    @77
    @98
    ve
    cI
    @104
    rexbidv
    elab
    @68
    @98
    @42
    ve
    cI
    @68
    @71
    cI
    wcel
    #
    @98
    wa
    #
    wa
    #
    @38
    @71
    cP
    csg
    cfv
    #
    co
    #
    @71
    cP
    cplusg
    cfv
    #
    co
    #
    @38
    cI
    @108
    cP
    cgrp
    wcel
    #
    @66
    @71
    @12
    wcel
    @112
    @38
    wceq
    @108
    @58
    @113
    @108
    wph
    @58
    @27
    wph
    @29
    @67
    @107
    simpll2
    #
    @60
    syl
    #
    cP
    ringgrp
    syl
    @108
    cJ
    @12
    @38
    @108
    wph
    @15
    @114
    @17
    syl
    @61
    @62
    @64
    @107
    simplrl
    #
    sseldd
    #
    @108
    cI
    @12
    @71
    @108
    wph
    cI
    @12
    wss
    #
    @114
    wph
    @59
    @118
    hbtlem3.i
    @12
    cI
    cU
    cP
    @16
    hbtlem.u
    lidlss
    syl
    syl
    @68
    @106
    @98
    simprl
    #
    sseldd
    #
    @12
    @111
    cP
    @109
    @38
    @71
    @16
    @111
    eqid
    #
    @109
    eqid
    #
    grpnpcan
    syl3anc
    @108
    @58
    @59
    @110
    cI
    wcel
    #
    @106
    @112
    cI
    wcel
    @115
    @61
    @59
    @67
    @107
    wph
    @27
    @59
    @29
    hbtlem3.i
    3ad2ant2
    ad2antrr
    @108
    @110
    @4
    cfv
    #
    @6
    clt
    wbr
    #
    @123
    @108
    @69
    @12
    @74
    @4
    cP
    cR
    @38
    @71
    @6
    @109
    @19
    hbtlem.p
    @16
    @122
    @27
    wph
    @29
    @67
    @107
    simpll1
    @108
    wph
    @54
    @114
    hbtlem3.r
    syl
    @117
    @61
    @62
    @64
    @107
    simplrr
    @120
    @68
    @106
    @73
    @97
    simprrl
    @69
    eqid
    @74
    eqid
    @68
    @106
    @73
    @97
    simprrr
    deg1sublt
    @108
    @110
    cJ
    wcel
    #
    @29
    @125
    @123
    wi
    #
    @108
    @58
    @14
    @62
    @71
    cJ
    wcel
    @126
    @115
    @108
    wph
    @14
    @114
    hbtlem3.j
    syl
    @116
    @108
    cI
    cJ
    @71
    @61
    cI
    cJ
    wss
    #
    @67
    @107
    wph
    @27
    @128
    @29
    hbtlem3.ij
    3ad2ant2
    ad2antrr
    @119
    sseldd
    cP
    cU
    cJ
    @109
    @38
    @71
    hbtlem.u
    @122
    lidlsubcl
    syl22anc
    @27
    wph
    @29
    @67
    @107
    simpll3
    @28
    @127
    va
    @110
    cJ
    @0
    @110
    wceq
    #
    @7
    @125
    @2
    @123
    @129
    @5
    @124
    @6
    clt
    @0
    @110
    @4
    fveq2
    breq1d
    @0
    @110
    cI
    eleq1
    imbi12d
    rspcva
    syl2anc
    mpd
    @119
    @111
    cP
    cU
    cI
    @110
    @71
    hbtlem.u
    @121
    lidlacl
    syl22anc
    eqeltrrd
    rexlimdvaa
    syl5bi
    mpd
    expr
    sylbid
    ralrimiva
    3exp
    a2d
    nn0ind
    @28
    va
    cJ
    rsp
    syl6com
    com23
    imp
    rexlimdv
    mpd
    ex
    ssrdv
    eqssd
end
