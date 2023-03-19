include "ccn.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cxko.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "crest.mm"
include "ccmp.mm"
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "cmpt2.mm"
include "crn.mm"
include "wral.mm"
include "wa.mm"
include "simpr.mm"
include "adantr.mm"
include "cnco.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "wceq.mm"
include "wrex.mm"
include "xkobval.mm"
include "abeq2i.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "imaeq1.mm"
include "imaco.mm"
include "syl6eq.mm"
include "sseq1d.mm"
include "elrab3.mm"
include "syl.mm"
include "wfun.mm"
include "cdm.mm"
include "cnf.mm"
include "ffun.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "ctop.mm"
include "ad2antrr.mm"
include "cntop1.mm"
include "simplrl.mm"
include "elpwid.mm"
include "simplrr.mm"
include "cnima.mm"
include "xkoopn.mm"
include "eqeltrd.mm"
include "imaeq2.mm"
include "mptpreima.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "cvv.mm"
include "ctopon.mm"
include "cfv.mm"
include "xkotopon.mm"
include "ovex.mm"
include "pwex.mm"
include "cxp.mm"
include "xkotf.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "a1i.mm"
include "cfi.mm"
include "ctg.mm"
include "cntop2.mm"
include "xkoval.mm"
include "subbascn.mm"
include "mpbir2and.mm"

theorem xkoco2cn
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cF: class F
  let vk: setvar k
  let vv: setvar v
  let vx: setvar x
  let vh: setvar h
  let vy: setvar y
  assume xkoco2cn.r: |- ( ph -> R e. Top )
  assume xkoco2cn.f: |- ( ph -> F e. ( S Cn T ) )

  disjoint g ph
  disjoint R g
  disjoint S g
  disjoint T g
  disjoint F g
  disjoint g k
  disjoint g v
  disjoint g x
  disjoint k v
  disjoint k x
  disjoint k ph
  disjoint v x
  disjoint ph v
  disjoint ph x
  disjoint g h
  disjoint g y
  disjoint h k
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint R h
  disjoint k y
  disjoint R k
  disjoint v y
  disjoint R v
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint S k
  disjoint S v
  disjoint S x
  disjoint T h
  disjoint T k
  disjoint T v
  disjoint T x
  disjoint T y
  disjoint F h
  disjoint F k
  disjoint F v
  disjoint F x
  assert |- ( ph -> ( g e. ( R Cn S ) |-> ( F o. g ) ) e. ( ( S ^ko R ) Cn ( T ^ko R ) ) )

  proof
    wph
    vg
    cR
    cS
    ccn
    co
    #
    cF
    vg
    cv
    #
    ccom
    #
    cmpt
    #
    cS
    cR
    cxko
    co
    #
    cT
    cR
    cxko
    co
    #
    ccn
    co
    wcel
    @0
    cR
    cT
    ccn
    co
    #
    @3
    wf
    @3
    ccnv
    #
    vx
    cv
    #
    cima
    #
    @4
    wcel
    #
    vx
    vk
    vv
    cR
    vy
    cv
    crest
    co
    ccmp
    wcel
    vy
    cR
    cuni
    #
    cpw
    #
    crab
    #
    cT
    vh
    cv
    #
    vk
    cv
    #
    cima
    #
    vv
    cv
    #
    wss
    #
    vh
    @6
    crab
    #
    cmpt2
    #
    crn
    #
    wral
    wph
    vg
    @0
    @2
    @6
    @3
    wph
    @1
    @0
    wcel
    #
    wa
    @22
    cF
    cS
    cT
    ccn
    co
    wcel
    #
    @2
    @6
    wcel
    #
    wph
    @22
    simpr
    wph
    @23
    @22
    xkoco2cn.f
    adantr
    @1
    cF
    cR
    cS
    cT
    cnco
    #
    syl2anc
    @3
    eqid
    #
    fmptd
    wph
    @10
    vx
    @21
    @8
    @21
    wcel
    cR
    @15
    crest
    co
    ccmp
    wcel
    #
    @8
    @19
    wceq
    #
    wa
    #
    vv
    cT
    wrex
    vk
    @12
    wrex
    #
    wph
    @10
    @30
    vx
    @21
    vy
    vv
    cR
    cT
    @20
    vh
    vk
    @13
    @11
    vx
    @11
    eqid
    #
    @13
    eqid
    #
    @20
    eqid
    #
    xkobval
    abeq2i
    wph
    @29
    @10
    vk
    vv
    @12
    cT
    wph
    @15
    @12
    wcel
    #
    @17
    cT
    wcel
    #
    wa
    #
    wa
    #
    @27
    @28
    @10
    @37
    @27
    wa
    #
    @10
    @28
    @2
    @19
    wcel
    #
    vg
    @0
    crab
    #
    @4
    wcel
    @38
    @40
    @1
    @15
    cima
    #
    cF
    ccnv
    @17
    cima
    #
    wss
    #
    vg
    @0
    crab
    @4
    @38
    @39
    @43
    vg
    @0
    @38
    @22
    wa
    #
    @39
    cF
    @41
    cima
    #
    @17
    wss
    #
    @43
    @44
    @24
    @39
    @46
    wb
    @44
    @22
    @23
    @24
    @38
    @22
    simpr
    #
    wph
    @23
    @36
    @27
    @22
    xkoco2cn.f
    ad3antrrr
    @25
    syl2anc
    @18
    @46
    vh
    @2
    @6
    @14
    @2
    wceq
    #
    @16
    @45
    @17
    @48
    @16
    @2
    @15
    cima
    @45
    @14
    @2
    @15
    imaeq1
    cF
    @1
    @15
    imaco
    syl6eq
    sseq1d
    elrab3
    syl
    @44
    cF
    wfun
    #
    @41
    cF
    cdm
    #
    wss
    @46
    @43
    wb
    @44
    cS
    cuni
    #
    cT
    cuni
    #
    cF
    wf
    #
    @49
    wph
    @53
    @36
    @27
    @22
    wph
    @23
    @53
    xkoco2cn.f
    cF
    cS
    cT
    @51
    @52
    @51
    eqid
    #
    @52
    eqid
    cnf
    syl
    ad3antrrr
    #
    @51
    @52
    cF
    ffun
    syl
    @44
    @41
    @51
    @50
    @44
    @41
    @1
    crn
    #
    @51
    @1
    @15
    imassrn
    @44
    @11
    @51
    @1
    wf
    #
    @56
    @51
    wss
    @44
    @22
    @57
    @47
    @1
    cR
    cS
    @11
    @51
    @31
    @54
    cnf
    syl
    @11
    @51
    @1
    frn
    syl
    syl5ss
    @44
    @53
    @50
    @51
    wceq
    @55
    @51
    @52
    cF
    fdm
    syl
    sseqtr4d
    @41
    @17
    cF
    funimass3
    syl2anc
    bitrd
    rabbidva
    @38
    @15
    cR
    cS
    @42
    vg
    @11
    @31
    wph
    cR
    ctop
    wcel
    #
    @36
    @27
    xkoco2cn.r
    ad2antrr
    wph
    cS
    ctop
    wcel
    #
    @36
    @27
    wph
    @23
    @59
    xkoco2cn.f
    cF
    cS
    cT
    cntop1
    syl
    #
    ad2antrr
    @38
    @15
    @11
    wph
    @34
    @35
    @27
    simplrl
    elpwid
    @37
    @27
    simpr
    @38
    @23
    @35
    @42
    cS
    wcel
    wph
    @23
    @36
    @27
    xkoco2cn.f
    ad2antrr
    wph
    @34
    @35
    @27
    simplrr
    @17
    cF
    cS
    cT
    cnima
    syl2anc
    xkoopn
    eqeltrd
    @28
    @9
    @40
    @4
    @28
    @9
    @7
    @19
    cima
    @40
    @8
    @19
    @7
    imaeq2
    vg
    @0
    @2
    @19
    @3
    @26
    mptpreima
    syl6eq
    eleq1d
    syl5ibrcom
    expimpd
    rexlimdvva
    syl5bi
    ralrimiv
    wph
    vx
    @21
    @3
    @4
    @5
    cvv
    @0
    @6
    wph
    @58
    @59
    @4
    @0
    ctopon
    cfv
    wcel
    xkoco2cn.r
    @60
    cR
    cS
    @4
    @4
    eqid
    xkotopon
    syl2anc
    @21
    cvv
    wcel
    wph
    @21
    @6
    cpw
    #
    @6
    cR
    cT
    ccn
    ovex
    pwex
    @13
    cT
    cxp
    #
    @61
    @20
    wf
    @21
    @61
    wss
    vy
    vv
    cR
    cT
    @20
    vh
    vk
    @13
    @11
    @31
    @32
    @33
    xkotf
    @62
    @61
    @20
    frn
    ax-mp
    ssexi
    a1i
    wph
    @58
    cT
    ctop
    wcel
    #
    @5
    @21
    cfi
    cfv
    ctg
    cfv
    wceq
    xkoco2cn.r
    wph
    @23
    @63
    xkoco2cn.f
    cF
    cS
    cT
    cntop2
    syl
    #
    vy
    vv
    cR
    cT
    @20
    vh
    vk
    @13
    @11
    @31
    @32
    @33
    xkoval
    syl2anc
    wph
    @58
    @63
    @5
    @6
    ctopon
    cfv
    wcel
    xkoco2cn.r
    @64
    cR
    cT
    @5
    @5
    eqid
    xkotopon
    syl2anc
    subbascn
    mpbir2and
end
