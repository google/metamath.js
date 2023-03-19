include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cres.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "csu.mm"
include "wceq.mm"
include "elpwinss.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "adantl.mm"
include "elinel2.mm"
include "wrex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "sselda.mm"
include "eliun.mm"
include "sylib.mm"
include "adantll.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfpw.mm"
include "nfin.mm"
include "nfel.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "cicc.mm"
include "simp3.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "wf.mm"
include "3expa.mm"
include "fmptd.mm"
include "3adant3.mm"
include "cr.mm"
include "sge0rern.mm"
include "fge0iccico.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "ad2antrr.mm"
include "rexlimd.mm"
include "mpd.mm"
include "sge0fsummpt.mm"
include "wss.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "iunin1.mm"
include "a1i.mm"
include "eqtr4d.mm"
include "syl.mm"
include "sumeq1d.mm"
include "simpl.mm"
include "adantlr.mm"
include "wdisj.mm"
include "adantr.mm"
include "cc.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sseldi.mm"
include "3adant1r.mm"
include "simpr.mm"
include "fsumiunss.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "csb.mm"
include "disjinfi.mm"
include "id.mm"
include "inss2.mm"
include "ssfi.mm"
include "ad2antlr.mm"
include "simpll.mm"
include "elrabi.mm"
include "elinel1.mm"
include "nfcsb1v.mm"
include "nf3an.mm"
include "nfim.mm"
include "eleq1.mm"
include "csbeq1a.mm"
include "eleq2d.mm"
include "3anbi23d.mm"
include "imbi1d.mm"
include "chvar.mm"
include "syl3anc.mm"
include "adantllr.mm"
include "fsumge0cl.mm"
include "rabid.mm"
include "simpld.mm"
include "mpteq2dva.mm"
include "nfrab1.mm"
include "nfsum.mm"
include "ineq1d.mm"
include "cbvmptf.mm"
include "eqtr2d.mm"
include "cbvsum.mm"
include "3eqtr4d.mm"
include "cxr.mm"
include "cvv.mm"
include "ssriv.mm"
include "ssexd.mm"
include "vex.mm"
include "inex2.mm"
include "icossicc.mm"
include "simplr.mm"
include "sge0cl.mm"
include "sylan2.mm"
include "nfmpt.mm"
include "nffv.mm"
include "mpteq1d.mm"
include "sge0xrcl.mm"
include "fveq2i.mm"
include "sge0lessmpt.mm"
include "eqbrtrd.mm"
include "cbvmpt.mm"
include "eqcomi.mm"
include "inss1.mm"
include "sge0lempt.mm"
include "xrletrd.mm"
include "ralrimiva.mm"
include "sge0lefi.mm"
include "mpbird.mm"
include "0xr.mm"
include "pnfxr.mm"
include "sge0ge0.mm"
include "clt.mm"
include "ltpnf.mm"
include "elicod.mm"
include "mptex2.mm"
include "fsumrecl.mm"
include "rexrd.mm"
include "crp.mm"
include "caddc.mm"
include "cxad.mm"
include "iunss1.mm"
include "disjss1.mm"
include "sylc.mm"
include "sge0iunmptlemfi.mm"
include "sge0ltfirpmpt.mm"
include "nfre1.mm"
include "sspwb.mm"
include "sseldd.mm"
include "elind.mm"
include "ad4ant24.mm"
include "elpwid.mm"
include "sge0ssrempt.mm"
include "rpxr.mm"
include "xaddcld.mm"
include "3ad2ant1.mm"
include "rpre.mm"
include "rexadd.mm"
include "breq12d.mm"
include "xrltled.mm"
include "rspe.mm"
include "sge0gerpmpt.mm"
include "xrletrid.mm"

theorem sge0iunmptlemre
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let cW: class W
  let vb: setvar b
  let vp: setvar p
  let vy: setvar y
  let vw: setvar w
  assume sge0iunmptlemre.a: |- ( ph -> A e. V )
  assume sge0iunmptlemre.b: |- ( ( ph /\ x e. A ) -> B e. W )
  assume sge0iunmptlemre.dj: |- ( ph -> Disj_ x e. A B )
  assume sge0iunmptlemre.c: |- ( ( ph /\ x e. A /\ k e. B ) -> C e. ( 0 [,] +oo ) )
  assume sge0iunmptlemre.re: |- ( ( ph /\ x e. A ) -> ( sum^ ` ( k e. B |-> C ) ) e. RR )
  assume sge0iunmptlemre.sxr: |- ( ph -> ( sum^ ` ( k e. U_ x e. A B |-> C ) ) e. RR* )
  assume sge0iunmptlemre.ssxr: |- ( ph -> ( sum^ ` ( x e. A |-> ( sum^ ` ( k e. B |-> C ) ) ) ) e. RR* )
  assume sge0iunmptlemre.f: |- ( ph -> ( k e. U_ x e. A B |-> C ) : U_ x e. A B --> ( 0 [,] +oo ) )
  assume sge0iunmptlemre.iue: |- ( ph -> U_ x e. A B e. _V )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B k
  disjoint C x
  disjoint W x
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A b
  disjoint A p
  disjoint A y
  disjoint b k
  disjoint b p
  disjoint b x
  disjoint b y
  disjoint k p
  disjoint k y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A w
  disjoint k w
  disjoint w x
  disjoint w y
  disjoint B b
  disjoint B p
  disjoint B y
  disjoint B w
  disjoint C b
  disjoint C p
  disjoint C y
  disjoint C w
  disjoint b ph
  disjoint p ph
  disjoint ph y
  disjoint ph w
  assert |- ( ph -> ( sum^ ` ( k e. U_ x e. A B |-> C ) ) = ( sum^ ` ( x e. A |-> ( sum^ ` ( k e. B |-> C ) ) ) ) )

  proof
    wph
    vk
    vx
    cA
    cB
    ciun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vx
    cA
    vk
    cB
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    sge0iunmptlemre.sxr
    sge0iunmptlemre.ssxr
    wph
    @2
    @6
    cle
    wbr
    @1
    vy
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    @6
    cle
    wbr
    #
    vy
    @0
    cpw
    #
    cfn
    cin
    #
    wral
    wph
    @10
    vy
    @12
    wph
    @7
    @12
    wcel
    #
    wa
    #
    @9
    vx
    cB
    @7
    cin
    #
    c0
    wne
    #
    vx
    cA
    crab
    #
    vk
    @15
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @6
    cle
    @14
    @9
    @17
    @15
    cC
    vk
    csu
    #
    vx
    csu
    #
    @21
    @14
    @9
    vk
    @7
    cC
    cmpt
    #
    csumge0
    cfv
    #
    @7
    cC
    vk
    csu
    #
    @23
    @13
    @9
    @25
    wceq
    wph
    @13
    @8
    @24
    csumge0
    @13
    vk
    @0
    @7
    cC
    @7
    @0
    cfn
    elpwinss
    #
    resmptd
    fveq2d
    adantl
    @14
    @7
    cC
    vk
    @13
    @7
    cfn
    wcel
    #
    wph
    @7
    @11
    cfn
    elinel2
    adantl
    #
    @14
    vk
    cv
    #
    @7
    wcel
    #
    wa
    #
    @30
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    cC
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @13
    @31
    @34
    wph
    @13
    @31
    wa
    @30
    @0
    wcel
    #
    @34
    @13
    @7
    @0
    @30
    @27
    sselda
    vx
    @30
    cA
    cB
    eliun
    sylib
    adantll
    @32
    @33
    @36
    vx
    cA
    @14
    @31
    vx
    wph
    @13
    vx
    wph
    vx
    nfv
    #
    vx
    @7
    @12
    vx
    @7
    nfcv
    #
    vx
    @11
    cfn
    vx
    @0
    vx
    cA
    cB
    nfiu1
    nfpw
    vx
    cfn
    nfcv
    nfin
    nfel
    nfan
    @31
    vx
    nfv
    nfan
    @36
    vx
    nfv
    #
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @33
    @36
    wi
    wi
    @13
    @31
    wph
    @42
    @33
    @36
    wph
    @42
    @33
    w3a
    #
    cC
    @30
    @3
    cfv
    #
    @35
    @43
    @44
    cC
    @43
    @33
    cC
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @44
    cC
    wceq
    wph
    @42
    @33
    simp3
    #
    sge0iunmptlemre.c
    vk
    cB
    cC
    @45
    @3
    @3
    eqid
    #
    fvmpt2
    syl2anc
    eqcomd
    @43
    cB
    @35
    @30
    @3
    @43
    @3
    cB
    wph
    @42
    cB
    @45
    @3
    wf
    #
    @33
    wph
    @42
    wa
    #
    vk
    cB
    cC
    @45
    @3
    wph
    @42
    @33
    @46
    sge0iunmptlemre.c
    3expa
    #
    @48
    fmptd
    #
    3adant3
    #
    @43
    @3
    cW
    cB
    wph
    @42
    cB
    cW
    wcel
    #
    @33
    sge0iunmptlemre.b
    3adant3
    @53
    wph
    @42
    @4
    cr
    wcel
    #
    @33
    sge0iunmptlemre.re
    3adant3
    sge0rern
    fge0iccico
    @47
    ffvelrnd
    eqeltrd
    #
    3exp
    ad2antrr
    rexlimd
    mpd
    sge0fsummpt
    @14
    @26
    vx
    cA
    @15
    ciun
    #
    cC
    vk
    csu
    #
    @23
    @13
    @26
    @58
    wceq
    wph
    @13
    @7
    @57
    cC
    vk
    @13
    @7
    @0
    wss
    #
    @7
    @57
    wceq
    @27
    @59
    @7
    @0
    @7
    cin
    #
    @57
    @59
    @60
    @7
    @59
    @60
    @7
    wceq
    @7
    @0
    sseqin2
    biimpi
    eqcomd
    @57
    @60
    wceq
    @59
    vx
    cA
    @7
    cB
    iunin1
    a1i
    eqtr4d
    syl
    sumeq1d
    adantl
    @14
    wph
    @28
    @58
    @23
    wceq
    wph
    @13
    simpl
    #
    @29
    wph
    @28
    wa
    #
    vx
    cA
    cB
    cC
    @7
    vk
    cW
    wph
    @42
    @54
    @28
    sge0iunmptlemre.b
    adantlr
    #
    wph
    vx
    cA
    cB
    wdisj
    #
    @28
    sge0iunmptlemre.dj
    adantr
    #
    wph
    @42
    @33
    cC
    cc
    wcel
    @28
    @43
    @35
    cc
    cC
    @35
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    @56
    sseldi
    3adant1r
    wph
    @28
    simpr
    #
    fsumiunss
    syl2anc
    eqtrd
    3eqtrd
    @14
    @21
    @23
    @14
    wph
    @28
    @21
    @23
    wceq
    @61
    @29
    @62
    vw
    @17
    vx
    vw
    cv
    #
    cB
    csb
    #
    @7
    cin
    #
    cC
    vk
    csu
    #
    cmpt
    #
    csumge0
    cfv
    #
    @17
    @70
    vw
    csu
    #
    @21
    @23
    @62
    @17
    @70
    vw
    @62
    vx
    cA
    cB
    @7
    cW
    @63
    @65
    @66
    disjinfi
    @62
    @67
    @17
    wcel
    #
    wa
    @69
    cC
    vk
    @28
    @69
    cfn
    wcel
    #
    wph
    @74
    @28
    @28
    @69
    @7
    wss
    #
    @75
    @28
    id
    #
    @76
    @28
    @68
    @7
    inss2
    a1i
    @7
    @69
    ssfi
    syl2anc
    ad2antlr
    wph
    @74
    @30
    @69
    wcel
    #
    @36
    @28
    wph
    @74
    wa
    #
    @78
    wa
    wph
    @67
    cA
    wcel
    #
    @30
    @68
    wcel
    #
    @36
    wph
    @74
    @78
    simpll
    @74
    @80
    wph
    @78
    @16
    vx
    @67
    cA
    elrabi
    #
    ad2antlr
    @78
    @81
    @79
    @30
    @68
    @7
    elinel1
    #
    adantl
    @43
    @36
    wi
    wph
    @80
    @81
    w3a
    #
    @36
    wi
    vx
    vw
    @84
    @36
    vx
    wph
    @80
    @81
    vx
    @38
    @80
    vx
    nfv
    vx
    @30
    @68
    vx
    @30
    nfcv
    vx
    @67
    cB
    nfcsb1v
    #
    nfel
    nf3an
    @40
    nfim
    @41
    @67
    wceq
    #
    @43
    @84
    @36
    @86
    @42
    @80
    @33
    @81
    wph
    @41
    @67
    cA
    eleq1
    @86
    cB
    @68
    @30
    vx
    @67
    cB
    csbeq1a
    #
    eleq2d
    3anbi23d
    imbi1d
    @56
    chvar
    #
    syl3anc
    adantllr
    fsumge0cl
    sge0fsummpt
    @62
    @72
    @21
    @62
    @71
    @20
    csumge0
    @62
    @20
    vx
    @17
    @22
    cmpt
    #
    @71
    @62
    vx
    @17
    @19
    @22
    @62
    @41
    @17
    wcel
    #
    wa
    @15
    cC
    vk
    @28
    @15
    cfn
    wcel
    #
    wph
    @90
    @28
    @28
    @15
    @7
    wss
    #
    @91
    @77
    @92
    @28
    cB
    @7
    inss2
    a1i
    @7
    @15
    ssfi
    syl2anc
    ad2antlr
    wph
    @90
    @30
    @15
    wcel
    #
    @36
    @28
    wph
    @90
    wa
    #
    @93
    wa
    wph
    @42
    @33
    @36
    wph
    @90
    @93
    simpll
    @90
    @42
    wph
    @93
    @90
    @42
    @16
    @90
    @42
    @16
    wa
    @16
    vx
    cA
    rabid
    biimpi
    simpld
    ad2antlr
    @93
    @33
    @94
    @30
    cB
    @7
    elinel1
    #
    adantl
    @56
    syl3anc
    adantllr
    sge0fsummpt
    mpteq2dva
    @89
    @71
    wceq
    @62
    vx
    vw
    @17
    @22
    @70
    @16
    vx
    cA
    nfrab1
    #
    vw
    @17
    nfcv
    #
    vw
    @22
    nfcv
    #
    vx
    @69
    cC
    vk
    vx
    @68
    @7
    @85
    @39
    nfin
    #
    vx
    cC
    nfcv
    #
    nfsum
    #
    @86
    @15
    @69
    cC
    vk
    @86
    cB
    @68
    @7
    @87
    ineq1d
    #
    sumeq1d
    #
    cbvmptf
    a1i
    eqtr2d
    fveq2d
    eqcomd
    @23
    @73
    wceq
    @62
    @17
    @22
    @70
    vx
    vw
    @103
    @97
    @96
    @98
    @101
    cbvsum
    a1i
    3eqtr4d
    syl2anc
    eqcomd
    eqtrd
    @14
    @21
    vw
    cA
    vk
    @69
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @6
    wph
    @21
    cxr
    wcel
    @13
    wph
    @20
    cvv
    @17
    wph
    @17
    cA
    cV
    sge0iunmptlemre.a
    @17
    cA
    wss
    wph
    vw
    @17
    cA
    @82
    ssriv
    a1i
    #
    ssexd
    wph
    vw
    @17
    @105
    @45
    @20
    @74
    wph
    @80
    @105
    @45
    wcel
    @82
    wph
    @80
    wa
    #
    @104
    cvv
    @69
    @69
    cvv
    wcel
    @109
    @7
    @68
    vy
    vex
    #
    inex2
    a1i
    @109
    vk
    @69
    cC
    @45
    @104
    @109
    @78
    wa
    #
    @35
    @45
    cC
    cc0
    cpnf
    icossicc
    @111
    wph
    @80
    @81
    @36
    wph
    @80
    @78
    simpll
    wph
    @80
    @78
    simplr
    @78
    @81
    @109
    @83
    adantl
    @88
    syl3anc
    sseldi
    @104
    eqid
    fmptd
    sge0cl
    #
    sylan2
    vx
    vw
    @17
    @19
    @105
    @96
    @97
    vw
    @19
    nfcv
    #
    vx
    @104
    csumge0
    vx
    csumge0
    nfcv
    vx
    vk
    @69
    cC
    @99
    @100
    nfmpt
    nffv
    #
    @86
    @18
    @104
    csumge0
    @86
    vk
    @15
    @69
    cC
    @102
    mpteq1d
    fveq2d
    #
    cbvmptf
    #
    fmptd
    sge0xrcl
    adantr
    wph
    @107
    cxr
    wcel
    @13
    wph
    @106
    cV
    cA
    sge0iunmptlemre.a
    wph
    vw
    cA
    @105
    @45
    @106
    @112
    @106
    eqid
    fmptd
    sge0xrcl
    adantr
    @14
    wph
    @6
    cxr
    wcel
    @61
    sge0iunmptlemre.ssxr
    syl
    wph
    @21
    @107
    cle
    wbr
    @13
    wph
    @21
    vw
    @17
    @105
    cmpt
    #
    csumge0
    cfv
    #
    @107
    cle
    @21
    @118
    wceq
    wph
    @20
    @117
    csumge0
    @116
    fveq2i
    a1i
    wph
    vw
    cA
    @105
    @17
    cV
    sge0iunmptlemre.a
    @112
    @108
    sge0lessmpt
    eqbrtrd
    adantr
    wph
    @107
    @6
    cle
    wbr
    @13
    wph
    @107
    vx
    cA
    @19
    cmpt
    #
    csumge0
    cfv
    #
    @6
    cle
    @107
    @120
    wceq
    wph
    @106
    @119
    csumge0
    @119
    @106
    vx
    vw
    cA
    @19
    @105
    @113
    @114
    @115
    cbvmpt
    eqcomi
    fveq2i
    a1i
    wph
    vx
    cA
    @19
    @4
    cV
    @38
    sge0iunmptlemre.a
    @50
    @18
    cvv
    @15
    @15
    cvv
    wcel
    @50
    @7
    cB
    @110
    inex2
    a1i
    @50
    vk
    @15
    cC
    @45
    @18
    @93
    @50
    @33
    @46
    @95
    @51
    sylan2
    @18
    eqid
    fmptd
    sge0cl
    @50
    @3
    cW
    cB
    sge0iunmptlemre.b
    @52
    sge0cl
    #
    @50
    vk
    cB
    cC
    @15
    cW
    sge0iunmptlemre.b
    @51
    @15
    cB
    wss
    @50
    cB
    @7
    inss1
    a1i
    sge0lessmpt
    sge0lempt
    eqbrtrd
    adantr
    xrletrd
    eqbrtrd
    ralrimiva
    wph
    vy
    @6
    @1
    cvv
    @0
    sge0iunmptlemre.iue
    sge0iunmptlemre.f
    sge0iunmptlemre.ssxr
    sge0lefi
    mpbird
    wph
    @6
    @2
    cle
    wbr
    @5
    @7
    cres
    #
    csumge0
    cfv
    #
    @2
    cle
    wbr
    #
    vy
    cA
    cpw
    #
    cfn
    cin
    #
    wral
    wph
    @124
    vy
    @126
    wph
    @7
    @126
    wcel
    #
    wa
    #
    @123
    @7
    @4
    vx
    csu
    #
    @2
    cle
    @128
    @123
    vx
    @7
    @4
    cmpt
    #
    csumge0
    cfv
    #
    @129
    @127
    @123
    @131
    wceq
    wph
    @127
    @122
    @130
    csumge0
    @127
    vx
    cA
    @7
    @4
    @7
    cA
    cfn
    elpwinss
    #
    resmptd
    fveq2d
    adantl
    @128
    @7
    @4
    vx
    @127
    @28
    wph
    @7
    @125
    cfn
    elinel2
    adantl
    #
    @128
    @41
    @7
    wcel
    #
    wa
    #
    cc0
    cpnf
    @4
    cc0
    cxr
    wcel
    @135
    0xr
    a1i
    cpnf
    cxr
    wcel
    @135
    pnfxr
    a1i
    @135
    @3
    cW
    cB
    @135
    wph
    @42
    @54
    wph
    @127
    @134
    simpll
    #
    @127
    @134
    @42
    wph
    @127
    @7
    cA
    @41
    @132
    sselda
    adantll
    #
    sge0iunmptlemre.b
    syl2anc
    #
    @135
    wph
    @42
    @49
    @136
    @137
    @52
    syl2anc
    #
    sge0xrcl
    @135
    @3
    cW
    cB
    @138
    @139
    sge0ge0
    @135
    @55
    @4
    cpnf
    clt
    wbr
    @135
    wph
    @42
    @55
    @136
    @137
    sge0iunmptlemre.re
    syl2anc
    #
    @4
    ltpnf
    syl
    elicod
    sge0fsummpt
    #
    eqtrd
    @128
    vk
    vp
    vb
    @0
    cC
    @129
    cvv
    @128
    vk
    nfv
    wph
    @0
    cvv
    wcel
    @127
    sge0iunmptlemre.iue
    adantr
    #
    wph
    @37
    @46
    @127
    wph
    vk
    @0
    cC
    @45
    sge0iunmptlemre.f
    mptex2
    #
    adantlr
    @128
    @129
    @128
    @7
    @4
    vx
    @133
    @140
    fsumrecl
    #
    rexrd
    #
    @128
    vp
    cv
    #
    crp
    wcel
    #
    wa
    #
    vk
    vx
    @7
    cB
    ciun
    #
    cC
    cmpt
    csumge0
    cfv
    #
    vk
    vb
    cv
    #
    cC
    cmpt
    csumge0
    cfv
    #
    @146
    caddc
    co
    #
    clt
    wbr
    #
    vb
    @149
    cpw
    #
    cfn
    cin
    #
    wrex
    @129
    @152
    @146
    cxad
    co
    #
    cle
    wbr
    #
    vb
    @12
    wrex
    #
    @148
    vk
    vb
    @149
    cC
    cvv
    @146
    @148
    vk
    nfv
    @128
    @149
    cvv
    wcel
    #
    @147
    @128
    @149
    @0
    cvv
    @142
    @127
    @149
    @0
    wss
    #
    wph
    @127
    @7
    cA
    wss
    #
    @161
    @132
    vx
    @7
    cA
    cB
    iunss1
    #
    syl
    adantl
    #
    ssexd
    #
    adantr
    @128
    @30
    @149
    wcel
    #
    @46
    @147
    @128
    @166
    wa
    wph
    @37
    @46
    wph
    @127
    @166
    simpll
    @128
    @149
    @0
    @30
    @164
    sselda
    @143
    syl2anc
    #
    adantlr
    @128
    @147
    simpr
    @128
    @150
    cr
    wcel
    #
    @147
    @128
    @150
    @131
    cr
    @128
    vx
    @7
    cB
    cC
    vk
    cW
    @133
    @138
    @128
    @162
    @64
    vx
    @7
    cB
    wdisj
    @127
    @162
    wph
    @132
    adantl
    wph
    @64
    @127
    sge0iunmptlemre.dj
    adantr
    vx
    @7
    cA
    cB
    disjss1
    sylc
    @128
    @134
    @33
    w3a
    wph
    @42
    @33
    @46
    @128
    @134
    wph
    @33
    @136
    3adant3
    @128
    @134
    @42
    @33
    @137
    3adant3
    @128
    @134
    @33
    simp3
    sge0iunmptlemre.c
    syl3anc
    @140
    sge0iunmptlemfi
    #
    @128
    @131
    @129
    cr
    @141
    @144
    eqeltrd
    eqeltrd
    #
    adantr
    sge0ltfirpmpt
    @148
    @154
    @159
    vb
    @156
    @148
    vb
    nfv
    @158
    vb
    @12
    nfre1
    @148
    @151
    @156
    wcel
    #
    @154
    @159
    @148
    @171
    @154
    w3a
    #
    @151
    @12
    wcel
    #
    @158
    @159
    @148
    @171
    @173
    @154
    @127
    @171
    @173
    wph
    @147
    @127
    @171
    wa
    #
    @11
    cfn
    @151
    @174
    @155
    @11
    @151
    @127
    @155
    @11
    wss
    #
    @171
    @127
    @162
    @175
    @132
    @162
    @161
    @175
    @163
    @161
    @175
    @149
    @0
    sspwb
    biimpi
    syl
    syl
    adantr
    @171
    @151
    @155
    wcel
    @127
    @151
    @155
    cfn
    elinel1
    #
    adantl
    sseldd
    @171
    @151
    cfn
    wcel
    @127
    @151
    @155
    cfn
    elinel2
    adantl
    elind
    ad4ant24
    3adant3
    @172
    @129
    @157
    @148
    @171
    @129
    cxr
    wcel
    #
    @154
    @128
    @177
    @147
    @171
    @145
    ad2antrr
    3adant3
    @148
    @171
    @157
    cxr
    wcel
    @154
    @148
    @171
    wa
    #
    @152
    @146
    @128
    @171
    @152
    cxr
    wcel
    @147
    @128
    @171
    wa
    #
    @152
    @179
    vk
    @149
    cC
    @151
    cvv
    @179
    vk
    nfv
    @128
    @160
    @171
    @165
    adantr
    @128
    @166
    @46
    @171
    @167
    adantlr
    @128
    @168
    @171
    @170
    adantr
    @171
    @151
    @149
    wss
    @128
    @171
    @151
    @149
    @176
    elpwid
    adantl
    sge0ssrempt
    #
    rexrd
    adantlr
    @147
    @146
    cxr
    wcel
    @128
    @171
    @146
    rpxr
    ad2antlr
    xaddcld
    3adant3
    @172
    @129
    @157
    clt
    wbr
    @154
    @148
    @171
    @154
    simp3
    @172
    @129
    @150
    @157
    @153
    clt
    @148
    @171
    @129
    @150
    wceq
    #
    @154
    @128
    @181
    @147
    @128
    @150
    @131
    @129
    @169
    @141
    eqtr2d
    adantr
    3ad2ant1
    @148
    @171
    @157
    @153
    wceq
    #
    @154
    @178
    @152
    cr
    wcel
    #
    @146
    cr
    wcel
    #
    @182
    @128
    @171
    @183
    @147
    @180
    adantlr
    @147
    @184
    @128
    @171
    @146
    rpre
    ad2antlr
    @152
    @146
    rexadd
    syl2anc
    3adant3
    breq12d
    mpbird
    xrltled
    @158
    vb
    @12
    rspe
    syl2anc
    3exp
    rexlimd
    mpd
    sge0gerpmpt
    eqbrtrd
    ralrimiva
    wph
    vy
    @2
    @5
    cV
    cA
    sge0iunmptlemre.a
    wph
    vx
    cA
    @4
    @45
    @5
    @121
    @5
    eqid
    fmptd
    sge0iunmptlemre.sxr
    sge0lefi
    mpbird
    xrletrid
end
