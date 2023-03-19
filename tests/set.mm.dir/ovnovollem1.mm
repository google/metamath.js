include "cr.mm"
include "cxp.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cico.mm"
include "cfv.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wf.mm"
include "cop.mm"
include "eqidd.mm"
include "wb.mm"
include "adantr.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "fsng.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "snssd.mm"
include "fssd.mm"
include "cvv.mm"
include "reex.mm"
include "xpex.mm"
include "a1i.mm"
include "snex.mm"
include "elmapd.mm"
include "fmptd.mm"
include "ovexd.mm"
include "nnex.mm"
include "crn.mm"
include "cuni.mm"
include "wfn.mm"
include "cxr.mm"
include "cpw.mm"
include "icof.mm"
include "rexpssxrxp.mm"
include "fcoss.mm"
include "ffnd.mm"
include "fniunfv.mm"
include "eqcomd.mm"
include "sseqtrd.mm"
include "fvex.mm"
include "iunex.mm"
include "snn0d.mm"
include "mapss2.mm"
include "mpbid.mm"
include "nfv.mm"
include "fvexd.mm"
include "iunmapsn.mm"
include "wfun.mm"
include "cdm.mm"
include "elmapfun.mm"
include "simpr.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "iuneq2dv.mm"
include "oveq1d.mm"
include "ffun.mm"
include "id.mm"
include "fvmpt2.mm"
include "adantl.mm"
include "funeqd.mm"
include "dmeqd.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "fveq1d.mm"
include "ad2antlr.mm"
include "elsni.mm"
include "fveq2d.mm"
include "fvsng.mm"
include "ad2antrr.mm"
include "3eqtrd.mm"
include "ixpeq2dva.mm"
include "ixpconst.mm"
include "3eqtr4d.mm"
include "c1st.mm"
include "c2nd.mm"
include "nfcv.mm"
include "ressxr.mm"
include "xpss2.mm"
include "ax-mp.mm"
include "volicofmpt.mm"
include "cc.mm"
include "coeq2d.mm"
include "snidg.mm"
include "dmsnopg.mm"
include "eleqtrrd.mm"
include "1st2nd2.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "volicore.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "fveq2.mm"
include "prodsn.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "jca.mm"
include "fveq1.mm"
include "ixpeq2dv.mm"
include "iuneq2d.mm"
include "sseq2d.mm"
include "simpl.mm"
include "prodeq2dv.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"

theorem ovnovollem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  assume ovnovollem1.a: |- ( ph -> A e. V )
  assume ovnovollem1.f: |- ( ph -> F e. ( ( RR X. RR ) ^m NN ) )
  assume ovnovollem1.i: |- I = ( j e. NN |-> { <. A , ( F ` j ) >. } )
  assume ovnovollem1.s: |- ( ph -> B C_ U. ran ( [,) o. F ) )
  assume ovnovollem1.b: |- ( ph -> B e. W )
  assume ovnovollem1.z: |- ( ph -> Z = ( sum^ ` ( ( vol o. [,) ) o. F ) ) )

  disjoint A i
  disjoint A j
  disjoint A k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint B i
  disjoint F j
  disjoint F k
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint V k
  disjoint Z i
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> E. i e. ( ( ( RR X. RR ) ^m { A } ) ^m NN ) ( ( B ^m { A } ) C_ U_ j e. NN X_ k e. { A } ( ( [,) o. ( i ` j ) ) ` k ) /\ Z = ( sum^ ` ( j e. NN |-> prod_ k e. { A } ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) )

  proof
    wph
    cI
    cr
    cr
    cxp
    #
    cA
    csn
    #
    cmap
    co
    #
    cn
    cmap
    co
    #
    wcel
    #
    cB
    @1
    cmap
    co
    #
    vj
    cn
    vk
    @1
    vk
    cv
    #
    cico
    vj
    cv
    #
    cI
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    cZ
    vj
    cn
    @1
    @10
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    @5
    vj
    cn
    vk
    @1
    @6
    cico
    @7
    vi
    cv
    #
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    cZ
    vj
    cn
    @1
    @23
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vi
    @3
    wrex
    wph
    @4
    cn
    @2
    cI
    wf
    wph
    vj
    cn
    cA
    @7
    cF
    cfv
    #
    cop
    #
    csn
    #
    @2
    cI
    wph
    @7
    cn
    wcel
    #
    wa
    #
    @35
    @2
    wcel
    @1
    @0
    @35
    wf
    #
    @37
    @1
    @33
    csn
    #
    @0
    @35
    @37
    @1
    @39
    @35
    wf
    #
    @35
    @35
    wceq
    #
    @37
    @35
    eqidd
    @37
    cA
    cV
    wcel
    #
    @33
    @0
    wcel
    #
    @40
    @41
    wb
    wph
    @42
    @36
    ovnovollem1.a
    adantr
    #
    wph
    cn
    @0
    @7
    cF
    wph
    cF
    @0
    cn
    cmap
    co
    wcel
    #
    cn
    @0
    cF
    wf
    #
    ovnovollem1.f
    cF
    @0
    cn
    elmapi
    syl
    #
    ffvelrnda
    #
    cA
    @33
    cV
    @0
    @35
    fsng
    syl2anc
    mpbird
    #
    @37
    @33
    @0
    @48
    snssd
    fssd
    #
    @37
    @0
    @1
    @35
    cvv
    cvv
    @0
    cvv
    wcel
    @37
    cr
    cr
    reex
    reex
    xpex
    a1i
    @1
    cvv
    wcel
    #
    @37
    cA
    snex
    #
    a1i
    elmapd
    mpbird
    ovnovollem1.i
    fmptd
    wph
    @2
    cn
    cI
    cvv
    cvv
    wph
    @0
    @1
    cmap
    ovexd
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    elmapd
    mpbird
    wph
    @13
    @18
    wph
    @5
    vj
    cn
    @7
    cico
    cF
    ccom
    #
    cfv
    #
    ciun
    #
    @1
    cmap
    co
    #
    @12
    wph
    cB
    @56
    wss
    @5
    @57
    wss
    wph
    cB
    @54
    crn
    cuni
    #
    @56
    ovnovollem1.s
    wph
    @56
    @58
    wph
    @54
    cn
    wfn
    @56
    @58
    wceq
    wph
    cn
    cxr
    cpw
    #
    @54
    wph
    cxr
    cxr
    cxp
    #
    @59
    @0
    cn
    cico
    cF
    @60
    @59
    cico
    wf
    wph
    icof
    a1i
    @0
    @60
    wss
    wph
    rexpssxrxp
    a1i
    @47
    fcoss
    ffnd
    vj
    cn
    @54
    fniunfv
    syl
    eqcomd
    sseqtrd
    wph
    cB
    @56
    @1
    cW
    cvv
    cvv
    ovnovollem1.b
    @56
    cvv
    wcel
    wph
    vj
    cn
    @55
    nnex
    @7
    @54
    fvex
    iunex
    a1i
    @51
    wph
    @52
    a1i
    wph
    cA
    cV
    ovnovollem1.a
    snn0d
    mapss2
    mpbid
    wph
    vj
    cn
    @33
    cico
    cfv
    #
    ciun
    #
    @1
    cmap
    co
    #
    vj
    cn
    @61
    @1
    cmap
    co
    #
    ciun
    #
    @57
    @12
    wph
    @65
    @63
    wph
    vj
    cn
    @61
    cA
    cvv
    cvv
    cV
    wph
    vj
    nfv
    @53
    @37
    @33
    cico
    fvexd
    ovnovollem1.a
    iunmapsn
    eqcomd
    wph
    @56
    @62
    @1
    cmap
    wph
    vj
    cn
    @55
    @61
    @37
    cF
    wfun
    #
    @7
    cF
    cdm
    #
    wcel
    @55
    @61
    wceq
    wph
    @66
    @36
    wph
    @45
    @66
    ovnovollem1.f
    cF
    @0
    cn
    elmapfun
    syl
    adantr
    @37
    @7
    cn
    @67
    wph
    @36
    simpr
    wph
    cn
    @67
    wceq
    @36
    wph
    @67
    cn
    wph
    @46
    @67
    cn
    wceq
    @47
    cn
    @0
    cF
    fdm
    syl
    eqcomd
    adantr
    eleqtrd
    @7
    cico
    cF
    fvco
    syl2anc
    iuneq2dv
    oveq1d
    wph
    vj
    cn
    @11
    @64
    @37
    @11
    vk
    @1
    @61
    cixp
    #
    @64
    @37
    vk
    @1
    @10
    @61
    @37
    @6
    @1
    wcel
    #
    wa
    #
    @10
    @6
    @8
    cfv
    #
    cico
    cfv
    #
    @61
    @61
    @70
    @8
    wfun
    #
    @6
    @8
    cdm
    #
    wcel
    #
    @10
    @72
    wceq
    @37
    @73
    @69
    @37
    @73
    @35
    wfun
    #
    @37
    @40
    @76
    @49
    @1
    @39
    @35
    ffun
    syl
    #
    @37
    @8
    @35
    @36
    @8
    @35
    wceq
    #
    wph
    @36
    @36
    @35
    cvv
    wcel
    #
    @78
    @36
    id
    @79
    @36
    @34
    snex
    a1i
    vj
    cn
    @35
    cvv
    cI
    ovnovollem1.i
    fvmpt2
    syl2anc
    #
    adantl
    #
    funeqd
    mpbird
    adantr
    @70
    @75
    @69
    @37
    @69
    simpr
    @37
    @75
    @69
    wb
    @69
    @37
    @74
    @1
    @6
    @37
    @74
    @35
    cdm
    #
    @1
    @37
    @8
    @35
    @81
    dmeqd
    @37
    @38
    @82
    @1
    wceq
    #
    @50
    @1
    @0
    @35
    fdm
    syl
    eqtrd
    eleq2d
    adantr
    mpbird
    @6
    cico
    @8
    fvco
    syl2anc
    @70
    @71
    @33
    cico
    @70
    @71
    @6
    @35
    cfv
    #
    cA
    @35
    cfv
    #
    @33
    @36
    @71
    @84
    wceq
    wph
    @69
    @36
    @6
    @8
    @35
    @80
    fveq1d
    ad2antlr
    @69
    @84
    @85
    wceq
    @37
    @69
    @6
    cA
    @35
    @6
    cA
    elsni
    fveq2d
    adantl
    wph
    @85
    @33
    wceq
    #
    @36
    @69
    wph
    @42
    @33
    cvv
    wcel
    #
    @86
    ovnovollem1.a
    wph
    @7
    cF
    fvexd
    #
    cA
    @33
    cV
    cvv
    fvsng
    #
    syl2anc
    ad2antrr
    3eqtrd
    fveq2d
    @70
    @61
    eqidd
    3eqtrd
    ixpeq2dva
    @68
    @64
    wceq
    @37
    vk
    @1
    @61
    @52
    @33
    cico
    fvex
    ixpconst
    a1i
    eqtrd
    iuneq2dv
    3eqtr4d
    sseqtrd
    wph
    cZ
    cvol
    cico
    ccom
    cF
    ccom
    #
    csumge0
    cfv
    @17
    ovnovollem1.z
    wph
    @90
    @16
    csumge0
    wph
    @90
    vj
    cn
    @33
    c1st
    cfv
    #
    @33
    c2nd
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    @16
    wph
    vj
    cn
    cF
    vj
    cF
    nfcv
    wph
    cn
    @0
    cr
    cxr
    cxp
    #
    cF
    @47
    @0
    @95
    wss
    #
    wph
    cr
    cxr
    wss
    @96
    ressxr
    cr
    cxr
    cr
    xpss2
    ax-mp
    a1i
    fssd
    volicofmpt
    wph
    vj
    cn
    @94
    @15
    @37
    @15
    cA
    @9
    cfv
    #
    cvol
    cfv
    #
    @94
    @37
    @42
    @98
    cc
    wcel
    @15
    @98
    wceq
    @44
    @37
    @98
    @37
    @98
    @94
    cr
    @37
    @97
    @93
    cvol
    @37
    @97
    cA
    cico
    @35
    ccom
    #
    cfv
    #
    @85
    cico
    cfv
    #
    @93
    @36
    @97
    @100
    wceq
    wph
    @36
    cA
    @9
    @99
    @36
    @8
    @35
    cico
    @80
    coeq2d
    fveq1d
    adantl
    @37
    @76
    cA
    @82
    wcel
    #
    @100
    @101
    wceq
    @77
    wph
    @102
    @36
    wph
    cA
    @1
    @82
    wph
    @42
    cA
    @1
    wcel
    ovnovollem1.a
    cA
    cV
    snidg
    syl
    wph
    @87
    @83
    @88
    cA
    @33
    cvv
    dmsnopg
    syl
    eleqtrrd
    adantr
    cA
    cico
    @35
    fvco
    syl2anc
    @37
    @101
    @91
    @92
    cop
    #
    cico
    cfv
    #
    @93
    @37
    @85
    @103
    cico
    @37
    @85
    @33
    @103
    @37
    @42
    @87
    @86
    @44
    @37
    @7
    cF
    fvexd
    @89
    syl2anc
    @37
    @43
    @33
    @103
    wceq
    @48
    @33
    cr
    cr
    1st2nd2
    syl
    eqtrd
    fveq2d
    @104
    @93
    wceq
    @37
    @93
    @104
    @91
    @92
    cico
    df-ov
    eqcomi
    a1i
    eqtrd
    3eqtrd
    fveq2d
    #
    @37
    @91
    cr
    wcel
    #
    @92
    cr
    wcel
    #
    @94
    cr
    wcel
    @37
    @43
    @106
    @48
    @33
    cr
    cr
    xp1st
    syl
    @37
    @43
    @107
    @48
    @33
    cr
    cr
    xp2nd
    syl
    @91
    @92
    volicore
    syl2anc
    eqeltrd
    recnd
    @14
    @98
    vk
    cA
    cV
    @6
    cA
    wceq
    @10
    @97
    cvol
    @6
    cA
    @9
    fveq2
    fveq2d
    prodsn
    syl2anc
    @105
    eqtr2d
    mpteq2dva
    eqtrd
    fveq2d
    eqtrd
    jca
    @32
    @19
    vi
    cI
    @3
    @20
    cI
    wceq
    #
    @26
    @13
    @31
    @18
    @108
    @25
    @12
    @5
    @108
    vj
    cn
    @24
    @11
    @108
    vk
    @1
    @23
    @10
    @108
    @6
    @22
    @9
    @108
    @21
    @8
    cico
    @7
    @20
    cI
    fveq1
    coeq2d
    fveq1d
    ixpeq2dv
    iuneq2d
    sseq2d
    @108
    @30
    @17
    cZ
    @108
    @29
    @16
    csumge0
    @108
    vj
    cn
    @28
    @15
    @108
    @1
    @27
    @14
    vk
    @108
    @69
    wa
    #
    @23
    @10
    cvol
    @109
    @6
    @22
    @9
    @109
    @21
    @8
    cico
    @109
    @7
    @20
    cI
    @108
    @69
    simpl
    fveq1d
    coeq2d
    fveq1d
    fveq2d
    prodeq2dv
    mpteq2dv
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
end
