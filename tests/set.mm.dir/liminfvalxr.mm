include "clsi.mm"
include "cfv.mm"
include "cv.mm"
include "cxne.mm"
include "cmpt.mm"
include "clsp.mm"
include "cr.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "cinf.mm"
include "crn.mm"
include "csup.mm"
include "wceq.mm"
include "wtru.mm"
include "nftru.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "inss2.mm"
include "infxrcl.mm"
include "ax-mp.mm"
include "a1i.mm"
include "supminfxrrnmpt.mm"
include "trud.mm"
include "crab.mm"
include "tru.mm"
include "supminfxr2.mm"
include "w3a.mm"
include "wrex.mm"
include "elinel1.mm"
include "nfmpt1.mm"
include "wfn.mm"
include "xnegex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "adantr.mm"
include "simpr.mm"
include "fvelimad.mm"
include "3adant2.mm"
include "syl3an3.mm"
include "wi.mm"
include "elinel2.mm"
include "cvv.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "adantll.mm"
include "eqcom.mm"
include "biimpi.mm"
include "adantl.mm"
include "wb.mm"
include "simplr.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "adantlr.mm"
include "xneg11.mm"
include "mpbid.mm"
include "wfun.mm"
include "cdm.mm"
include "ffund.mm"
include "anim12i.mm"
include "simpld.mm"
include "fdmd.mm"
include "eleqtrd.mm"
include "jca.mm"
include "funfvima.mm"
include "sylc.mm"
include "ad4ant13.mm"
include "eqeltrd.mm"
include "syldan.mm"
include "rexlimdva2.mm"
include "3adant3.mm"
include "mpd.mm"
include "rabssdv.mm"
include "ssrab2.mm"
include "ssind.mm"
include "ffnd.mm"
include "fvelima2.mm"
include "xnegeqd.mm"
include "simpl.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "reximdv.mm"
include "syl.mm"
include "elmptima.mm"
include "sylibr.mm"
include "sselda.mm"
include "xnegcld.mm"
include "elind.mm"
include "ssrabdv.mm"
include "eqssd.mm"
include "infeq1d.mm"
include "eqtr2d.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "fexd.mm"
include "liminfval.mm"
include "mptexd.mm"
include "limsupval.mm"
include "3eqtr4d.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfxneg.mm"
include "fveq2.mm"
include "cbvmpt.mm"
include "fveq2i.mm"
include "xnegeqi.mm"

theorem liminfvalxr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  assume liminfvalxr.1: |- F/_ x F
  assume liminfvalxr.2: |- ( ph -> A e. V )
  assume liminfvalxr.3: |- ( ph -> F : A --> RR* )

  disjoint A x
  disjoint A k
  disjoint A y
  disjoint A z
  disjoint k y
  disjoint k z
  disjoint y z
  disjoint x y
  disjoint F k
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( liminf ` F ) = -e ( limsup ` ( x e. A |-> -e ( F ` x ) ) ) )

  proof
    wph
    cF
    clsi
    cfv
    #
    vy
    cA
    vy
    cv
    #
    cF
    cfv
    #
    cxne
    #
    cmpt
    #
    clsp
    cfv
    #
    cxne
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cxne
    #
    cmpt
    #
    clsp
    cfv
    #
    cxne
    #
    wph
    vk
    cr
    cF
    vk
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    crn
    cxr
    clt
    csup
    #
    vk
    cr
    @4
    @14
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cxne
    #
    @0
    @6
    wph
    @19
    vk
    cr
    @17
    cxne
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cxne
    #
    @26
    @19
    @31
    wceq
    #
    wph
    @32
    wtru
    vk
    cr
    @17
    vk
    nftru
    @17
    cxr
    wcel
    #
    wtru
    @13
    cr
    wcel
    wa
    @16
    cxr
    wss
    #
    @33
    @15
    cxr
    inss2
    #
    @16
    infxrcl
    ax-mp
    a1i
    supminfxrrnmpt
    trud
    a1i
    wph
    @30
    @25
    wph
    cxr
    @29
    @24
    clt
    wph
    @28
    @23
    wph
    vk
    cr
    @27
    @22
    wph
    @22
    vz
    cv
    #
    cxne
    #
    @21
    wcel
    #
    vz
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cxne
    #
    @27
    @22
    @41
    wceq
    #
    wph
    wtru
    @42
    tru
    wtru
    vz
    @21
    @21
    cxr
    wss
    wtru
    @20
    cxr
    inss2
    a1i
    supminfxr2
    ax-mp
    a1i
    wph
    @40
    @17
    wph
    cxr
    @39
    @16
    clt
    wph
    @39
    @16
    wph
    @39
    @15
    cxr
    wph
    @38
    vz
    cxr
    @15
    wph
    @36
    cxr
    wcel
    #
    @38
    w3a
    @1
    @4
    cfv
    #
    @37
    wceq
    #
    vy
    cA
    @14
    cin
    #
    wrex
    #
    @36
    @15
    wcel
    #
    @38
    wph
    @43
    @37
    @20
    wcel
    #
    @47
    @37
    @20
    cxr
    elinel1
    wph
    @49
    @47
    @43
    wph
    @49
    wa
    vy
    cA
    @14
    @37
    @4
    vy
    cA
    @3
    nfmpt1
    wph
    @4
    cA
    wfn
    #
    @49
    @50
    wph
    vy
    cA
    @3
    @4
    @2
    xnegex
    #
    @4
    eqid
    #
    fnmpti
    a1i
    adantr
    wph
    @49
    simpr
    fvelimad
    3adant2
    syl3an3
    @38
    wph
    @43
    @37
    cxr
    wcel
    #
    @47
    @48
    wi
    #
    @37
    @20
    cxr
    elinel2
    wph
    @43
    @54
    @53
    wph
    @43
    wa
    #
    @45
    @48
    vy
    @46
    @55
    @1
    @46
    wcel
    #
    wa
    #
    @45
    @3
    @37
    wceq
    #
    @48
    @56
    @45
    @58
    @55
    @56
    @45
    wa
    @3
    @44
    @37
    @56
    @3
    @44
    wceq
    @45
    @56
    @44
    @3
    @56
    @1
    cA
    wcel
    #
    @3
    cvv
    wcel
    #
    @44
    @3
    wceq
    @1
    cA
    @14
    elinel1
    #
    @60
    @56
    @51
    a1i
    vy
    cA
    @3
    cvv
    @4
    @52
    fvmpt2
    syl2anc
    eqcomd
    adantr
    @56
    @45
    simpr
    eqtrd
    adantll
    @57
    @58
    wa
    #
    @36
    @2
    @15
    @62
    @37
    @3
    wceq
    #
    @36
    @2
    wceq
    #
    @58
    @63
    @57
    @58
    @63
    @3
    @37
    eqcom
    biimpi
    adantl
    @57
    @63
    @64
    wb
    #
    @58
    @57
    @43
    @2
    cxr
    wcel
    #
    @65
    wph
    @43
    @56
    simplr
    wph
    @56
    @66
    @43
    wph
    @56
    wa
    #
    cA
    cxr
    @1
    cF
    wph
    cA
    cxr
    cF
    wf
    @56
    liminfvalxr.3
    adantr
    @56
    @59
    wph
    @61
    adantl
    #
    ffvelrnd
    adantlr
    @36
    @2
    xneg11
    #
    syl2anc
    adantr
    mpbid
    wph
    @56
    @2
    @15
    wcel
    #
    @43
    @58
    @67
    cF
    wfun
    #
    @1
    cF
    cdm
    #
    wcel
    #
    wa
    @1
    @14
    wcel
    #
    @70
    @67
    @71
    @73
    @67
    @71
    @59
    wph
    @71
    @56
    @59
    wph
    cA
    cxr
    cF
    liminfvalxr.3
    ffund
    @61
    anim12i
    simpld
    @67
    @1
    cA
    @72
    @68
    wph
    cA
    @72
    wceq
    @56
    wph
    @72
    cA
    wph
    cA
    cxr
    cF
    liminfvalxr.3
    fdmd
    eqcomd
    adantr
    eleqtrd
    jca
    @56
    @74
    wph
    @1
    cA
    @14
    elinel2
    adantl
    @14
    @1
    cF
    funfvima
    sylc
    ad4ant13
    eqeltrd
    syldan
    rexlimdva2
    3adant3
    syl3an3
    mpd
    rabssdv
    @39
    cxr
    wss
    wph
    @38
    vz
    cxr
    ssrab2
    a1i
    ssind
    wph
    @38
    vz
    cxr
    @16
    @34
    wph
    @35
    a1i
    #
    wph
    @36
    @16
    wcel
    #
    wa
    #
    @20
    cxr
    @37
    @77
    @63
    vy
    @46
    wrex
    #
    @49
    @77
    @2
    @36
    wceq
    #
    vy
    @46
    wrex
    #
    @78
    @77
    cF
    cA
    wfn
    #
    @48
    @80
    wph
    @81
    @76
    wph
    cA
    cxr
    cF
    liminfvalxr.3
    ffnd
    adantr
    @76
    @48
    wph
    @36
    @15
    cxr
    elinel1
    adantl
    vy
    cA
    @36
    @14
    cF
    fvelima2
    syl2anc
    @76
    @80
    @78
    wi
    #
    wph
    @76
    @43
    @82
    @36
    @15
    cxr
    elinel2
    @43
    @79
    @63
    vy
    @46
    @43
    @79
    @63
    @43
    @79
    wa
    #
    @36
    @2
    @83
    @63
    @64
    @83
    @36
    @2
    @79
    @64
    @43
    @79
    @64
    @2
    @36
    eqcom
    biimpi
    adantl
    #
    xnegeqd
    @83
    @43
    @66
    @65
    @43
    @79
    simpl
    #
    @83
    @36
    @2
    cxr
    @84
    @85
    eqeltrrd
    @69
    syl2anc
    mpbid
    xnegeqd
    ex
    reximdv
    syl
    adantl
    mpd
    @37
    cvv
    wcel
    @49
    @78
    wb
    @36
    xnegex
    vy
    cA
    @3
    @37
    @14
    cvv
    elmptima
    ax-mp
    sylibr
    @77
    @36
    wph
    @16
    cxr
    @36
    @75
    sselda
    xnegcld
    elind
    ssrabdv
    eqssd
    infeq1d
    xnegeqd
    eqtr2d
    mpteq2dv
    rneqd
    infeq1d
    xnegeqd
    eqtrd
    wph
    cF
    cvv
    wcel
    @0
    @19
    wceq
    wph
    cA
    cxr
    cV
    cF
    liminfvalxr.3
    liminfvalxr.2
    fexd
    vk
    cF
    @18
    cvv
    @18
    eqid
    liminfval
    syl
    wph
    @5
    @25
    wph
    @4
    cvv
    wcel
    @5
    @25
    wceq
    wph
    vy
    cA
    @3
    cV
    liminfvalxr.2
    mptexd
    vk
    @4
    @23
    cvv
    @23
    eqid
    limsupval
    syl
    xnegeqd
    3eqtr4d
    @6
    @12
    wceq
    wph
    @5
    @11
    @4
    @10
    clsp
    vy
    vx
    cA
    @3
    @9
    vx
    @2
    vx
    @1
    cF
    liminfvalxr.1
    vx
    @1
    nfcv
    nffv
    nfxneg
    vy
    @9
    nfcv
    @1
    @7
    wceq
    @2
    @8
    @1
    @7
    cF
    fveq2
    xnegeqd
    cbvmpt
    fveq2i
    xnegeqi
    a1i
    eqtrd
end
