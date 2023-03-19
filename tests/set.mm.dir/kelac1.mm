include "cv.mm"
include "cixp.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cuni.mm"
include "weq.mm"
include "cif.mm"
include "ciin.mm"
include "cin.mm"
include "wss.mm"
include "wral.mm"
include "wceq.mm"
include "wa.mm"
include "ccld.mm"
include "cfv.mm"
include "eqid.mm"
include "cldss.mm"
include "syl.mm"
include "ralrimiva.mm"
include "boxriin.mm"
include "cmpt.mm"
include "cpt.mm"
include "cvv.mm"
include "ctop.mm"
include "wf.mm"
include "ccmp.mm"
include "cmptop.mm"
include "wn.mm"
include "0ntop.mm"
include "fvprc.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "3syl.mm"
include "fmptd.mm"
include "dmfex.mm"
include "syl2anc.mm"
include "ptunimpt.mm"
include "ineq1d.mm"
include "topcld.mm"
include "ifcld.mm"
include "ptcldmpt.mm"
include "adantr.mm"
include "cfn.mm"
include "wrex.mm"
include "simprr.mm"
include "cima.mm"
include "wf1o.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "eqcomd.mm"
include "wfn.mm"
include "wb.mm"
include "f1ofn.mm"
include "ssid.mm"
include "fnimaeq0.mm"
include "sylancl.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eqnetrd.mm"
include "n0.mm"
include "sylib.mm"
include "rexv.mm"
include "sylibr.mm"
include "wi.mm"
include "ssralv.mm"
include "mpan9.mm"
include "eleq1.mm"
include "ac6sfi.mm"
include "ad2antrr.mm"
include "wel.mm"
include "cdif.mm"
include "cun.mm"
include "iftrue.mm"
include "ad2antrl.mm"
include "simpll.mm"
include "simprl.mm"
include "sselda.mm"
include "sseld.mm"
include "impr.mm"
include "eqeltrd.mm"
include "expr.mm"
include "ralimdva.mm"
include "imp.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "adantl.mm"
include "eldifi.mm"
include "sylan2.mm"
include "ralun.mm"
include "undif.mm"
include "biimpi.mm"
include "raleqdv.mm"
include "mpbid.mm"
include "mptelixpg.mm"
include "eleq2.mm"
include "simplrr.mm"
include "ifbothda.mm"
include "adantlr.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "a1i.mm"
include "simpr.mm"
include "simplr.mm"
include "disjne.mm"
include "syl3anc.mm"
include "neneqd.mm"
include "3eltr4d.mm"
include "ad3antrrr.mm"
include "mptexg.mm"
include "eliin.mm"
include "elind.mm"
include "ne0i.mm"
include "adantrl.mm"
include "exlimddv.mm"
include "cmpfiiin.mm"
include "ccnv.mm"
include "elixp2.mm"
include "simp3bi.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "ffvelrn.mm"
include "ex.mm"
include "4syl.mm"

theorem kelac1
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cI: class I
  let cJ: class J
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume kelac1.z: |- ( ( ph /\ x e. I ) -> S =/= (/) )
  assume kelac1.j: |- ( ( ph /\ x e. I ) -> J e. Top )
  assume kelac1.c: |- ( ( ph /\ x e. I ) -> C e. ( Clsd ` J ) )
  assume kelac1.b: |- ( ( ph /\ x e. I ) -> B : S -1-1-onto-> C )
  assume kelac1.u: |- ( ( ph /\ x e. I ) -> U e. U. J )
  assume kelac1.k: |- ( ph -> ( Xt_ ` ( x e. I |-> J ) ) e. Comp )

  disjoint ph x
  disjoint I x
  disjoint f ph
  disjoint ph y
  disjoint ph z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C f
  disjoint C w
  disjoint f w
  disjoint C y
  disjoint C z
  disjoint I f
  disjoint I y
  disjoint I z
  disjoint J f
  disjoint J y
  disjoint J z
  disjoint S y
  disjoint U y
  disjoint w x
  assert |- ( ph -> X_ x e. I S =/= (/) )

  proof
    wph
    vy
    cv
    #
    vx
    cI
    cC
    cixp
    #
    wcel
    #
    vx
    cI
    cS
    cixp
    #
    c0
    wne
    #
    vy
    wph
    @1
    c0
    wne
    @2
    vy
    wex
    wph
    @1
    vx
    cI
    cJ
    cuni
    #
    cixp
    #
    vy
    cI
    vx
    cI
    vx
    vy
    weq
    #
    cC
    @5
    cif
    #
    cixp
    #
    ciin
    #
    cin
    #
    c0
    wph
    cC
    @5
    wss
    #
    vx
    cI
    wral
    @1
    @11
    wceq
    wph
    @12
    vx
    cI
    wph
    vx
    cv
    #
    cI
    wcel
    #
    wa
    #
    cC
    cJ
    ccld
    cfv
    #
    wcel
    @12
    kelac1.c
    cC
    cJ
    @5
    @5
    eqid
    #
    cldss
    syl
    #
    ralrimiva
    vx
    vy
    cC
    @5
    cI
    boxriin
    syl
    wph
    @11
    vx
    cI
    cJ
    cmpt
    #
    cpt
    cfv
    #
    cuni
    #
    @10
    cin
    c0
    wph
    @6
    @21
    @10
    wph
    cI
    cvv
    wcel
    #
    cJ
    ctop
    wcel
    #
    vx
    cI
    wral
    @6
    @21
    wceq
    wph
    @19
    cvv
    wcel
    #
    cI
    ctop
    @19
    wf
    @22
    wph
    @20
    ccmp
    wcel
    @20
    ctop
    wcel
    #
    @24
    kelac1.k
    @20
    cmptop
    @24
    @25
    @24
    wn
    #
    @25
    c0
    ctop
    wcel
    0ntop
    @26
    @20
    c0
    ctop
    @19
    cpt
    fvprc
    eleq1d
    mtbiri
    con4i
    3syl
    wph
    vx
    cI
    cJ
    ctop
    @19
    kelac1.j
    @19
    eqid
    fmptd
    cI
    ctop
    cvv
    @19
    dmfex
    syl2anc
    #
    wph
    @23
    vx
    cI
    kelac1.j
    ralrimiva
    vx
    cI
    @20
    cJ
    cvv
    @20
    eqid
    ptunimpt
    syl2anc
    #
    ineq1d
    wph
    @9
    vy
    cI
    @20
    @21
    vz
    @21
    eqid
    kelac1.k
    wph
    @9
    @20
    ccld
    cfv
    wcel
    @0
    cI
    wcel
    wph
    cI
    @8
    vx
    cJ
    cvv
    @27
    kelac1.j
    @15
    @7
    cC
    @5
    @16
    kelac1.c
    @15
    @23
    @5
    @16
    wcel
    kelac1.j
    cJ
    @5
    @17
    topcld
    syl
    ifcld
    ptcldmpt
    adantr
    wph
    vz
    cv
    #
    cI
    wss
    #
    @29
    cfn
    wcel
    #
    wa
    #
    wa
    #
    @29
    cvv
    vf
    cv
    #
    wf
    #
    @13
    @34
    cfv
    #
    cC
    wcel
    #
    vx
    @29
    wral
    #
    wa
    #
    @21
    vy
    @29
    @9
    ciin
    #
    cin
    #
    c0
    wne
    #
    vf
    @33
    @31
    vw
    cv
    #
    cC
    wcel
    #
    vw
    cvv
    wrex
    #
    vx
    @29
    wral
    #
    @39
    vf
    wex
    wph
    @30
    @31
    simprr
    wph
    @45
    vx
    cI
    wral
    #
    @32
    @46
    wph
    @45
    vx
    cI
    @15
    @44
    vw
    wex
    #
    @45
    @15
    cC
    c0
    wne
    @48
    @15
    cC
    cB
    cS
    cima
    #
    c0
    @15
    @49
    cC
    @15
    cS
    cC
    cB
    wf1o
    #
    cS
    cC
    cB
    wfo
    @49
    cC
    wceq
    kelac1.b
    cS
    cC
    cB
    f1ofo
    cS
    cC
    cB
    foima
    3syl
    eqcomd
    @15
    @49
    c0
    wne
    cS
    c0
    wne
    kelac1.z
    @15
    @49
    c0
    cS
    c0
    @15
    cB
    cS
    wfn
    #
    cS
    cS
    wss
    @49
    c0
    wceq
    cS
    c0
    wceq
    wb
    @15
    @50
    @51
    kelac1.b
    cS
    cC
    cB
    f1ofn
    syl
    cS
    ssid
    cS
    cS
    cB
    fnimaeq0
    sylancl
    necon3bid
    mpbird
    eqnetrd
    vw
    cC
    n0
    sylib
    @44
    vw
    rexv
    sylibr
    ralrimiva
    @30
    @47
    @46
    wi
    @31
    @45
    vx
    @29
    cI
    ssralv
    adantr
    mpan9
    @44
    @37
    vx
    vw
    @29
    cvv
    vf
    @43
    @36
    cC
    eleq1
    ac6sfi
    syl2anc
    @33
    @38
    @42
    @35
    @33
    @38
    wa
    #
    @41
    @6
    @40
    cin
    #
    c0
    wph
    @41
    @53
    wceq
    @32
    @38
    wph
    @21
    @6
    @40
    wph
    @6
    @21
    @28
    eqcomd
    ineq1d
    ad2antrr
    @52
    vx
    cI
    vx
    vz
    wel
    #
    @36
    cU
    cif
    #
    cmpt
    #
    @53
    wcel
    @53
    c0
    wne
    @52
    @6
    @40
    @56
    @52
    @56
    @6
    wcel
    #
    @55
    @5
    wcel
    #
    vx
    cI
    wral
    #
    @52
    @58
    vx
    @29
    cI
    @29
    cdif
    #
    cun
    #
    wral
    #
    @59
    @52
    @58
    vx
    @29
    wral
    #
    @58
    vx
    @60
    wral
    #
    @62
    @33
    @38
    @63
    @33
    @37
    @58
    vx
    @29
    @33
    @54
    @37
    @58
    @33
    @54
    @37
    wa
    wa
    #
    @55
    @36
    @5
    @54
    @55
    @36
    wceq
    @33
    @37
    @54
    @36
    cU
    iftrue
    ad2antrl
    #
    @33
    @54
    @37
    @36
    @5
    wcel
    #
    @33
    @54
    wa
    #
    cC
    @5
    @36
    @68
    wph
    @14
    @12
    wph
    @32
    @54
    simpll
    @33
    @29
    cI
    @13
    wph
    @30
    @31
    simprl
    sselda
    @18
    syl2anc
    sseld
    impr
    #
    eqeltrd
    expr
    ralimdva
    imp
    wph
    @64
    @32
    @38
    wph
    @58
    vx
    @60
    wph
    @13
    @60
    wcel
    #
    wa
    @55
    cU
    @5
    @70
    @55
    cU
    wceq
    #
    wph
    @70
    @54
    @36
    cU
    @13
    cI
    @29
    eldifn
    iffalsed
    #
    adantl
    @70
    wph
    @14
    cU
    @5
    wcel
    #
    @13
    cI
    @29
    eldifi
    kelac1.u
    sylan2
    #
    eqeltrd
    ralrimiva
    ad2antrr
    @58
    vx
    @29
    @60
    ralun
    syl2anc
    @33
    @62
    @59
    wb
    @38
    @33
    @58
    vx
    @61
    cI
    @30
    @61
    cI
    wceq
    #
    wph
    @31
    @30
    @75
    @29
    cI
    undif
    biimpi
    ad2antrl
    #
    raleqdv
    adantr
    mpbid
    @52
    @22
    @57
    @59
    wb
    wph
    @22
    @32
    @38
    @27
    ad2antrr
    vx
    cI
    @55
    @5
    cvv
    mptelixpg
    syl
    mpbird
    @52
    @56
    @40
    wcel
    #
    @56
    @9
    wcel
    #
    vy
    @29
    wral
    #
    @52
    @78
    vy
    @29
    @52
    vy
    vz
    wel
    #
    wa
    #
    @78
    @55
    @8
    wcel
    #
    vx
    cI
    wral
    #
    @81
    @82
    vx
    @61
    wral
    #
    @83
    @81
    @82
    vx
    @29
    wral
    #
    @82
    vx
    @60
    wral
    #
    @84
    @52
    @85
    @80
    @33
    @38
    @85
    @33
    @37
    @82
    vx
    @29
    @33
    @54
    @37
    @82
    @65
    @55
    @36
    @8
    @66
    @7
    @37
    @67
    @36
    @8
    wcel
    @65
    cC
    @5
    cC
    @8
    @36
    eleq2
    @5
    @8
    @36
    eleq2
    @33
    @54
    @37
    @7
    simplrr
    @65
    @67
    @7
    wn
    @69
    adantr
    ifbothda
    eqeltrd
    expr
    ralimdva
    imp
    adantr
    @33
    @80
    @86
    @38
    wph
    @80
    @86
    @32
    wph
    @80
    wa
    #
    @82
    vx
    @60
    @87
    @70
    wa
    #
    cU
    @5
    @55
    @8
    wph
    @70
    @73
    @80
    @74
    adantlr
    @70
    @71
    @87
    @72
    adantl
    @88
    @7
    cC
    @5
    @88
    @13
    @0
    @88
    @60
    @29
    cin
    #
    c0
    wceq
    #
    @70
    @80
    @13
    @0
    wne
    @90
    @88
    @89
    @29
    @60
    cin
    c0
    @60
    @29
    incom
    @29
    cI
    disjdif
    eqtri
    a1i
    @87
    @70
    simpr
    wph
    @80
    @70
    simplr
    @60
    @29
    @13
    @0
    disjne
    syl3anc
    neneqd
    iffalsed
    3eltr4d
    ralrimiva
    adantlr
    adantlr
    @82
    vx
    @29
    @60
    ralun
    syl2anc
    @33
    @84
    @83
    wb
    @38
    @80
    @33
    @82
    vx
    @61
    cI
    @76
    raleqdv
    ad2antrr
    mpbid
    @81
    @22
    @78
    @83
    wb
    wph
    @22
    @32
    @38
    @80
    @27
    ad3antrrr
    vx
    cI
    @55
    @8
    cvv
    mptelixpg
    syl
    mpbird
    ralrimiva
    @52
    @56
    cvv
    wcel
    #
    @77
    @79
    wb
    wph
    @91
    @32
    @38
    wph
    @22
    @91
    @27
    vx
    cI
    @55
    cvv
    mptexg
    syl
    ad2antrr
    vy
    @56
    @29
    @9
    cvv
    eliin
    syl
    mpbird
    elind
    @53
    @56
    ne0i
    syl
    eqnetrd
    adantrl
    exlimddv
    cmpfiiin
    eqnetrd
    eqnetrd
    vy
    @1
    n0
    sylib
    wph
    @2
    wa
    #
    vx
    cI
    @13
    @0
    cfv
    #
    cB
    ccnv
    #
    cfv
    #
    cmpt
    #
    @3
    wcel
    #
    @4
    @92
    @97
    @95
    cS
    wcel
    #
    vx
    cI
    wral
    #
    @2
    wph
    @93
    cC
    wcel
    #
    vx
    cI
    wral
    #
    @99
    @2
    @0
    cvv
    wcel
    @0
    cI
    wfn
    @101
    vx
    cI
    cC
    @0
    elixp2
    simp3bi
    wph
    @101
    @99
    wph
    @100
    @98
    vx
    cI
    @15
    @50
    cC
    cS
    @94
    wf1o
    cC
    cS
    @94
    wf
    #
    @100
    @98
    wi
    kelac1.b
    cS
    cC
    cB
    f1ocnv
    cC
    cS
    @94
    f1of
    @102
    @100
    @98
    cC
    cS
    @93
    @94
    ffvelrn
    ex
    4syl
    ralimdva
    imp
    sylan2
    wph
    @97
    @99
    wb
    #
    @2
    wph
    @22
    @103
    @27
    vx
    cI
    @95
    cS
    cvv
    mptelixpg
    syl
    adantr
    mpbird
    @3
    @96
    ne0i
    syl
    exlimddv
end
