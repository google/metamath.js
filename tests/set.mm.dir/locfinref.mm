include "cv.mm"
include "wf.mm"
include "crn.mm"
include "cref.mm"
include "wbr.mm"
include "clocfin.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wex.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "f0.mm"
include "simpr.mm"
include "feq2d.mm"
include "mpbiri.mm"
include "rn0.mm"
include "cvv.mm"
include "0ex.mm"
include "refref.mm"
include "ax-mp.mm"
include "eqbrtri.mm"
include "syl5breqr.mm"
include "csn.mm"
include "ctop.mm"
include "cin.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "wrex.mm"
include "wral.mm"
include "sn0top.mm"
include "a1i.mm"
include "eqidd.mm"
include "ral0.mm"
include "cuni.mm"
include "unisn.mm"
include "eqcomi.mm"
include "unieqi.mm"
include "uni0.mm"
include "eqtr2i.mm"
include "islocfin.mm"
include "syl3anbrc.mm"
include "adantr.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "3eqtr3g.mm"
include "wb.mm"
include "locfintop.mm"
include "0top.mm"
include "3syl.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "feq1.mm"
include "rneq.mm"
include "breq1d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "spcev.mm"
include "syl3anc.mm"
include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "locfinreflem.mm"
include "cdif.mm"
include "cxp.mm"
include "cun.mm"
include "simpl.mm"
include "simprl1.mm"
include "fdmrn.mm"
include "sylib.mm"
include "simprl3.mm"
include "fssd.mm"
include "fconstg.mm"
include "mp1i.mm"
include "0opn.mm"
include "ad2antrr.mm"
include "snssd.mm"
include "disjdif.mm"
include "fun2.mm"
include "syl21anc.mm"
include "simprl2.mm"
include "undif.mm"
include "simprrl.mm"
include "eqbrtrd.mm"
include "simprd.mm"
include "refun0.mm"
include "syl2anc.mm"
include "wo.mm"
include "rnxpss.mm"
include "sssn.mm"
include "mpbi.mm"
include "rnun.mm"
include "uneq2.mm"
include "syl5eq.mm"
include "un0.mm"
include "syl6eq.mm"
include "orim12i.mm"
include "mpjaodan.mm"
include "simprrr.mm"
include "eqeltrd.mm"
include "snfi.mm"
include "unissd.mm"
include "lfinun.mm"
include "wi.mm"
include "refrel.mm"
include "brrelex2i.mm"
include "difexg.mm"
include "p0ex.mm"
include "xpexg.mm"
include "mpan2.mm"
include "vex.mm"
include "unexg.mm"
include "mpan.mm"
include "spcegv.mm"
include "4syl.mm"
include "imp.mm"
include "syl13anc.mm"
include "exlimddv.mm"
include "pm2.61dane.mm"

theorem locfinref
  let wph: wff ph
  let cU: class U
  let vf: setvar f
  let cJ: class J
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vn: setvar n
  let vs: setvar s
  assume locfinref.x: |- X = U. J
  assume locfinref.1: |- ( ph -> U C_ J )
  assume locfinref.2: |- ( ph -> X = U. U )
  assume locfinref.3: |- ( ph -> V C_ J )
  assume locfinref.4: |- ( ph -> V Ref U )
  assume locfinref.5: |- ( ph -> V e. ( LocFin ` J ) )

  disjoint J f
  disjoint U f
  disjoint V f
  disjoint f ph
  disjoint J g
  disjoint J j
  disjoint J k
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint g j
  disjoint g k
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint U g
  disjoint U j
  disjoint U k
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint V g
  disjoint V j
  disjoint V k
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint g ph
  disjoint j ph
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint n s
  disjoint n x
  disjoint s x
  assert |- ( ph -> E. f ( f : U --> J /\ ran f Ref U /\ ran f e. ( LocFin ` J ) ) )

  proof
    wph
    cU
    cJ
    vf
    cv
    #
    wf
    #
    @0
    crn
    #
    cU
    cref
    wbr
    #
    @2
    cJ
    clocfin
    cfv
    #
    wcel
    #
    w3a
    #
    vf
    wex
    #
    cU
    c0
    wph
    cU
    c0
    wceq
    #
    wa
    #
    cU
    cJ
    c0
    wf
    #
    c0
    crn
    #
    cU
    cref
    wbr
    #
    @11
    @4
    wcel
    #
    @7
    @9
    @10
    c0
    cJ
    c0
    wf
    cJ
    f0
    @9
    cU
    c0
    cJ
    c0
    wph
    @8
    simpr
    #
    feq2d
    mpbiri
    @9
    @11
    c0
    cU
    cref
    @11
    c0
    c0
    cref
    rn0
    c0
    cvv
    wcel
    #
    c0
    c0
    cref
    wbr
    0ex
    c0
    cvv
    refref
    ax-mp
    eqbrtri
    @14
    syl5breqr
    @9
    @11
    c0
    csn
    #
    clocfin
    cfv
    #
    @4
    @9
    @16
    ctop
    wcel
    #
    c0
    c0
    wceq
    vx
    cv
    vn
    cv
    #
    wcel
    vs
    cv
    @19
    cin
    c0
    wne
    vs
    @11
    crab
    cfn
    wcel
    wa
    vn
    @16
    wrex
    #
    vx
    c0
    wral
    #
    @11
    @17
    wcel
    @18
    @9
    sn0top
    a1i
    @9
    c0
    eqidd
    @21
    @9
    @20
    vx
    ral0
    a1i
    vx
    @11
    vn
    @16
    c0
    c0
    vs
    @16
    cuni
    #
    c0
    c0
    0ex
    unisn
    eqcomi
    @11
    cuni
    c0
    cuni
    #
    c0
    @11
    c0
    rn0
    unieqi
    uni0
    eqtr2i
    islocfin
    syl3anbrc
    @9
    cJ
    @16
    clocfin
    @9
    cJ
    cuni
    #
    c0
    wceq
    #
    cJ
    @16
    wceq
    #
    @9
    cX
    @23
    @24
    c0
    @9
    cX
    cU
    cuni
    #
    @23
    wph
    cX
    @27
    wceq
    @8
    locfinref.2
    adantr
    @9
    cU
    c0
    @14
    unieqd
    eqtrd
    locfinref.x
    uni0
    3eqtr3g
    wph
    @25
    @26
    wb
    #
    @8
    wph
    cV
    @4
    wcel
    #
    cJ
    ctop
    wcel
    #
    @28
    locfinref.5
    cV
    cJ
    locfintop
    #
    cJ
    0top
    3syl
    adantr
    mpbid
    fveq2d
    eleqtrrd
    @6
    @10
    @12
    @13
    w3a
    vf
    c0
    0ex
    @0
    c0
    wceq
    #
    @1
    @10
    @3
    @12
    @5
    @13
    cU
    cJ
    @0
    c0
    feq1
    @32
    @2
    @11
    cU
    cref
    @0
    c0
    rneq
    #
    breq1d
    @32
    @2
    @11
    @4
    @33
    eleq1d
    3anbi123d
    spcev
    syl3anc
    wph
    cU
    c0
    wne
    #
    wa
    #
    vg
    cv
    #
    wfun
    #
    @36
    cdm
    #
    cU
    wss
    #
    @36
    crn
    #
    cJ
    wss
    #
    w3a
    #
    @40
    cU
    cref
    wbr
    #
    @40
    @4
    wcel
    #
    wa
    #
    wa
    #
    @7
    vg
    wph
    @46
    vg
    wex
    @34
    wph
    cU
    vg
    cJ
    cV
    cX
    locfinref.x
    locfinref.1
    locfinref.2
    locfinref.3
    locfinref.4
    locfinref.5
    locfinreflem
    adantr
    @35
    @46
    wa
    #
    @35
    cU
    cJ
    @36
    cU
    @38
    cdif
    #
    @16
    cxp
    #
    cun
    #
    wf
    #
    @50
    crn
    #
    cU
    cref
    wbr
    #
    @52
    @4
    wcel
    #
    @7
    @35
    @46
    simpl
    #
    @47
    @38
    @48
    cun
    #
    cJ
    @50
    wf
    #
    @51
    @47
    @38
    cJ
    @36
    wf
    @48
    cJ
    @49
    wf
    @38
    @48
    cin
    c0
    wceq
    #
    @57
    @47
    @38
    @40
    cJ
    @36
    @47
    @37
    @38
    @40
    @36
    wf
    @37
    @39
    @41
    @45
    @35
    simprl1
    @36
    fdmrn
    sylib
    @37
    @39
    @41
    @45
    @35
    simprl3
    fssd
    @47
    @48
    @16
    cJ
    @49
    @15
    @48
    @16
    @49
    wf
    @47
    0ex
    @48
    c0
    cvv
    fconstg
    mp1i
    @47
    c0
    cJ
    wph
    c0
    cJ
    wcel
    #
    @34
    @46
    wph
    @29
    @30
    @59
    locfinref.5
    @31
    cJ
    0opn
    3syl
    ad2antrr
    #
    snssd
    fssd
    @58
    @47
    @38
    cU
    disjdif
    a1i
    @38
    @48
    cJ
    @36
    @49
    fun2
    syl21anc
    @47
    @56
    cU
    cJ
    @50
    @47
    @39
    @56
    cU
    wceq
    @37
    @39
    @41
    @45
    @35
    simprl2
    @38
    cU
    undif
    sylib
    feq2d
    mpbid
    @47
    @52
    @40
    wceq
    #
    @53
    @52
    @40
    @16
    cun
    #
    wceq
    #
    @47
    @61
    wa
    #
    @52
    @40
    cU
    cref
    @47
    @61
    simpr
    #
    @47
    @43
    @61
    @35
    @42
    @43
    @44
    simprrl
    #
    adantr
    eqbrtrd
    @47
    @63
    wa
    #
    @52
    @62
    cU
    cref
    @47
    @63
    simpr
    #
    @47
    @62
    cU
    cref
    wbr
    #
    @63
    @47
    @43
    @34
    @69
    @66
    @47
    wph
    @34
    @55
    simprd
    @40
    cU
    refun0
    syl2anc
    adantr
    eqbrtrd
    @49
    crn
    #
    c0
    wceq
    #
    @70
    @16
    wceq
    #
    wo
    #
    @61
    @63
    wo
    @47
    @70
    @16
    wss
    @73
    @48
    @16
    rnxpss
    @70
    c0
    sssn
    mpbi
    @71
    @61
    @72
    @63
    @71
    @52
    @40
    c0
    cun
    #
    @40
    @71
    @52
    @40
    @70
    cun
    #
    @74
    @36
    @49
    rnun
    #
    @70
    c0
    @40
    uneq2
    syl5eq
    @40
    un0
    syl6eq
    @72
    @52
    @75
    @62
    @76
    @70
    @16
    @40
    uneq2
    syl5eq
    orim12i
    mp1i
    #
    mpjaodan
    @47
    @61
    @54
    @63
    @64
    @52
    @40
    @4
    @65
    @47
    @44
    @61
    @35
    @42
    @43
    @44
    simprrr
    #
    adantr
    eqeltrd
    @67
    @52
    @62
    @4
    @68
    @67
    @44
    @16
    cfn
    wcel
    #
    @22
    @24
    wss
    @62
    @4
    wcel
    @47
    @44
    @63
    @78
    adantr
    @79
    @67
    c0
    snfi
    a1i
    @67
    @16
    cJ
    @67
    c0
    cJ
    @47
    @59
    @63
    @60
    adantr
    snssd
    unissd
    @40
    @16
    cJ
    lfinun
    syl3anc
    eqeltrd
    @77
    mpjaodan
    @35
    @51
    @53
    @54
    w3a
    #
    @7
    @35
    @48
    cvv
    wcel
    #
    @49
    cvv
    wcel
    #
    @50
    cvv
    wcel
    #
    @80
    @7
    wi
    wph
    @81
    @34
    wph
    cV
    cU
    cref
    wbr
    cU
    cvv
    wcel
    @81
    locfinref.4
    cV
    cU
    cref
    refrel
    brrelex2i
    cU
    @38
    cvv
    difexg
    3syl
    adantr
    @81
    @16
    cvv
    wcel
    @82
    p0ex
    @48
    @16
    cvv
    cvv
    xpexg
    mpan2
    @36
    cvv
    wcel
    @82
    @83
    vg
    vex
    @36
    @49
    cvv
    cvv
    unexg
    mpan
    @6
    @80
    vf
    @50
    cvv
    @0
    @50
    wceq
    #
    @1
    @51
    @3
    @53
    @5
    @54
    cU
    cJ
    @0
    @50
    feq1
    @84
    @2
    @52
    cU
    cref
    @0
    @50
    rneq
    #
    breq1d
    @84
    @2
    @52
    @4
    @85
    eleq1d
    3anbi123d
    spcegv
    4syl
    imp
    syl13anc
    exlimddv
    pm2.61dane
end
