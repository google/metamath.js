include "cr.mm"
include "cxp.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cico.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cvol.mm"
include "csumge0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wf.mm"
include "csn.mm"
include "elmapi.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "snidg.mm"
include "fmptd.mm"
include "wb.mm"
include "reex.mm"
include "xpex.mm"
include "nnex.mm"
include "elmap.mm"
include "a1i.mm"
include "mpbird.mm"
include "ciun.mm"
include "cixp.mm"
include "elsni.mm"
include "fveq2d.mm"
include "adantl.mm"
include "wfun.mm"
include "cdm.mm"
include "elmapfun.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "syl2anc.mm"
include "cvv.mm"
include "id.mm"
include "fvexd.mm"
include "fvmpt2.mm"
include "ffund.mm"
include "dmmptd.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "ixpeq2dva.mm"
include "snex.mm"
include "fvex.mm"
include "ixpconst.mm"
include "iuneq2dv.mm"
include "nfv.mm"
include "iunmapsn.mm"
include "sseqtrd.mm"
include "iunex.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "mapss2.mm"
include "wfn.mm"
include "cxr.mm"
include "cpw.mm"
include "icof.mm"
include "rexpssxrxp.mm"
include "fcoss.mm"
include "ffnd.mm"
include "fniunfv.mm"
include "cprod.mm"
include "cmpt.mm"
include "c1st.mm"
include "c2nd.mm"
include "nfcv.mm"
include "ressxr.mm"
include "xpss2.mm"
include "ax-mp.mm"
include "fssd.mm"
include "volicofmpt.mm"
include "cc.mm"
include "cop.mm"
include "eqeltrd.mm"
include "1st2nd2.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "volicore.mm"
include "recnd.mm"
include "fveq2.mm"
include "prodsn.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "jca.mm"
include "coeq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"

theorem ovnovollem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  assume ovnovollem2.a: |- ( ph -> A e. V )
  assume ovnovollem2.b: |- ( ph -> B e. W )
  assume ovnovollem2.i: |- ( ph -> I e. ( ( ( RR X. RR ) ^m { A } ) ^m NN ) )
  assume ovnovollem2.s: |- ( ph -> ( B ^m { A } ) C_ U_ j e. NN X_ k e. { A } ( ( [,) o. ( I ` j ) ) ` k ) )
  assume ovnovollem2.z: |- ( ph -> Z = ( sum^ ` ( j e. NN |-> prod_ k e. { A } ( vol ` ( ( [,) o. ( I ` j ) ) ` k ) ) ) ) )
  assume ovnovollem2.f: |- F = ( j e. NN |-> ( ( I ` j ) ` A ) )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint B f
  disjoint F f
  disjoint F j
  disjoint F k
  disjoint I k
  disjoint V k
  disjoint Z f
  disjoint j ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> E. f e. ( ( RR X. RR ) ^m NN ) ( B C_ U. ran ( [,) o. f ) /\ Z = ( sum^ ` ( ( vol o. [,) ) o. f ) ) ) )

  proof
    wph
    cF
    cr
    cr
    cxp
    #
    cn
    cmap
    co
    #
    wcel
    #
    cB
    cico
    cF
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    cZ
    cvol
    cico
    ccom
    #
    cF
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    cB
    cico
    vf
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    cZ
    @7
    @12
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @1
    wrex
    wph
    @2
    cn
    @0
    cF
    wf
    #
    wph
    vj
    cn
    cA
    vj
    cv
    #
    cI
    cfv
    #
    cfv
    #
    @0
    cF
    wph
    @22
    cn
    wcel
    #
    wa
    #
    cA
    csn
    #
    @0
    cA
    @23
    @26
    @23
    @0
    @27
    cmap
    co
    #
    wcel
    #
    @27
    @0
    @23
    wf
    #
    @26
    cn
    @28
    @22
    cI
    wph
    cn
    @28
    cI
    wf
    #
    @25
    wph
    cI
    @28
    cn
    cmap
    co
    wcel
    @31
    ovnovollem2.i
    cI
    @28
    cn
    elmapi
    syl
    adantr
    wph
    @25
    simpr
    #
    ffvelrnd
    #
    @23
    @0
    @27
    elmapi
    syl
    #
    wph
    cA
    @27
    wcel
    #
    @25
    wph
    cA
    cV
    wcel
    #
    @35
    ovnovollem2.a
    cA
    cV
    snidg
    syl
    #
    adantr
    #
    ffvelrnd
    #
    ovnovollem2.f
    fmptd
    #
    @2
    @21
    wb
    wph
    @0
    cn
    cF
    cr
    cr
    reex
    reex
    xpex
    nnex
    elmap
    a1i
    mpbird
    wph
    @6
    @10
    wph
    cB
    vj
    cn
    @22
    @3
    cfv
    #
    ciun
    #
    @5
    wph
    cB
    @42
    wss
    cB
    @27
    cmap
    co
    #
    @42
    @27
    cmap
    co
    #
    wss
    wph
    @43
    vj
    cn
    vk
    @27
    vk
    cv
    #
    cico
    @23
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    @44
    ovnovollem2.s
    wph
    @49
    vj
    cn
    @41
    @27
    cmap
    co
    #
    ciun
    @44
    wph
    vj
    cn
    @48
    @50
    @26
    @48
    vk
    @27
    @41
    cixp
    #
    @50
    @26
    vk
    @27
    @47
    @41
    @26
    @45
    @27
    wcel
    #
    wa
    @47
    cA
    @46
    cfv
    #
    @24
    cico
    cfv
    #
    @41
    @52
    @47
    @53
    wceq
    @26
    @52
    @45
    cA
    @46
    @45
    cA
    elsni
    fveq2d
    adantl
    @26
    @53
    @54
    wceq
    #
    @52
    @26
    @23
    wfun
    #
    cA
    @23
    cdm
    #
    wcel
    @55
    @26
    @29
    @56
    @33
    @23
    @0
    @27
    elmapfun
    syl
    @26
    cA
    @27
    @57
    @38
    @26
    @57
    @27
    @26
    @30
    @57
    @27
    wceq
    @34
    @27
    @0
    @23
    fdm
    syl
    eqcomd
    eleqtrd
    cA
    cico
    @23
    fvco
    syl2anc
    #
    adantr
    @26
    @54
    @41
    wceq
    @52
    @26
    @54
    @22
    cF
    cfv
    #
    cico
    cfv
    #
    @41
    @25
    @54
    @60
    wceq
    wph
    @25
    @24
    @59
    cico
    @25
    @59
    @24
    @25
    @25
    @24
    cvv
    wcel
    #
    @59
    @24
    wceq
    #
    @25
    id
    @25
    cA
    @23
    fvexd
    vj
    cn
    @24
    cvv
    cF
    ovnovollem2.f
    fvmpt2
    #
    syl2anc
    eqcomd
    fveq2d
    adantl
    @26
    @41
    @60
    @26
    cF
    wfun
    #
    @22
    cF
    cdm
    #
    wcel
    @41
    @60
    wceq
    wph
    @64
    @25
    wph
    cn
    @0
    cF
    @40
    ffund
    adantr
    @26
    @22
    cn
    @65
    @32
    wph
    cn
    @65
    wceq
    @25
    wph
    @65
    cn
    wph
    vj
    cF
    cn
    @24
    @0
    ovnovollem2.f
    @39
    dmmptd
    eqcomd
    adantr
    eleqtrd
    @22
    cico
    cF
    fvco
    syl2anc
    #
    eqcomd
    eqtrd
    #
    adantr
    3eqtrd
    ixpeq2dva
    @51
    @50
    wceq
    @26
    vk
    @27
    @41
    cA
    snex
    #
    @22
    @3
    fvex
    #
    ixpconst
    a1i
    eqtrd
    iuneq2dv
    wph
    vj
    cn
    @41
    cA
    cvv
    cvv
    cV
    wph
    vj
    nfv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    @26
    @22
    @3
    fvexd
    ovnovollem2.a
    iunmapsn
    eqtrd
    sseqtrd
    wph
    cB
    @42
    @27
    cW
    cvv
    cvv
    ovnovollem2.b
    @42
    cvv
    wcel
    wph
    vj
    cn
    @41
    nnex
    @69
    iunex
    a1i
    @27
    cvv
    wcel
    wph
    @68
    a1i
    wph
    @35
    @27
    c0
    wne
    @37
    @27
    cA
    ne0i
    syl
    mapss2
    mpbird
    wph
    @3
    cn
    wfn
    @42
    @5
    wceq
    wph
    cn
    cxr
    cpw
    #
    @3
    wph
    cxr
    cxr
    cxp
    #
    @70
    @0
    cn
    cico
    cF
    @71
    @70
    cico
    wf
    wph
    icof
    a1i
    @0
    @71
    wss
    wph
    rexpssxrxp
    a1i
    @40
    fcoss
    ffnd
    vj
    cn
    @3
    fniunfv
    syl
    sseqtrd
    wph
    cZ
    vj
    cn
    @27
    @47
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
    @9
    ovnovollem2.z
    wph
    @8
    @74
    csumge0
    wph
    @8
    vj
    cn
    @59
    c1st
    cfv
    #
    @59
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
    @74
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
    @40
    @0
    @79
    wss
    #
    wph
    cr
    cxr
    wss
    @80
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
    @78
    @73
    @26
    @73
    @53
    cvol
    cfv
    #
    @78
    @26
    @36
    @81
    cc
    wcel
    @73
    @81
    wceq
    wph
    @36
    @25
    ovnovollem2.a
    adantr
    @26
    @81
    @26
    @81
    @78
    cr
    @26
    @53
    @77
    cvol
    @26
    @53
    @54
    @41
    @77
    @58
    @67
    @26
    @41
    @60
    @75
    @76
    cop
    #
    cico
    cfv
    #
    @77
    @66
    @26
    @59
    @82
    cico
    @26
    @59
    @0
    wcel
    #
    @59
    @82
    wceq
    @26
    @59
    @24
    @0
    @26
    @25
    @61
    @62
    @32
    @26
    cA
    @23
    fvexd
    @63
    syl2anc
    @39
    eqeltrd
    #
    @59
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @83
    @77
    wceq
    @26
    @77
    @83
    @75
    @76
    cico
    df-ov
    eqcomi
    a1i
    3eqtrd
    3eqtrd
    fveq2d
    #
    @26
    @75
    cr
    wcel
    #
    @76
    cr
    wcel
    #
    @78
    cr
    wcel
    @26
    @84
    @87
    @85
    @59
    cr
    cr
    xp1st
    syl
    @26
    @84
    @88
    @85
    @59
    cr
    cr
    xp2nd
    syl
    @75
    @76
    volicore
    syl2anc
    eqeltrd
    recnd
    @72
    @81
    vk
    cA
    cV
    @45
    cA
    wceq
    @47
    @53
    cvol
    @45
    cA
    @46
    fveq2
    fveq2d
    prodsn
    syl2anc
    @86
    eqtr2d
    mpteq2dva
    eqtrd
    fveq2d
    eqtr4d
    jca
    @20
    @11
    vf
    cF
    @1
    @12
    cF
    wceq
    #
    @16
    @6
    @19
    @10
    @89
    @15
    @5
    cB
    @89
    @14
    @4
    @89
    @13
    @3
    @12
    cF
    cico
    coeq2
    rneqd
    unieqd
    sseq2d
    @89
    @18
    @9
    cZ
    @89
    @17
    @8
    csumge0
    @12
    cF
    @7
    coeq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
end
