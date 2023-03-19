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
include "cnco.mm"
include "sylan.mm"
include "eqid.mm"
include "fmptd.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "xkobval.mm"
include "abeq2i.mm"
include "wb.mm"
include "ad2antrr.mm"
include "imaeq1.mm"
include "imaco.mm"
include "syl6eq.mm"
include "sseq1d.mm"
include "elrab3.mm"
include "syl.mm"
include "rabbidva.mm"
include "ctop.mm"
include "cntop2.mm"
include "imassrn.mm"
include "cnf.mm"
include "frn.mm"
include "3syl.mm"
include "syl5ss.mm"
include "imacmp.mm"
include "sylancom.mm"
include "simplrr.mm"
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
include "syl2anc.mm"
include "ovex.mm"
include "pwex.mm"
include "cxp.mm"
include "xkotf.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "a1i.mm"
include "cfi.mm"
include "ctg.mm"
include "cntop1.mm"
include "xkoval.mm"
include "subbascn.mm"
include "mpbir2and.mm"

theorem xkoco1cn
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
  assume xkoco1cn.t: |- ( ph -> T e. Top )
  assume xkoco1cn.f: |- ( ph -> F e. ( R Cn S ) )

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
  assert |- ( ph -> ( g e. ( S Cn T ) |-> ( g o. F ) ) e. ( ( T ^ko S ) Cn ( T ^ko R ) ) )

  proof
    wph
    vg
    cS
    cT
    ccn
    co
    #
    vg
    cv
    #
    cF
    ccom
    #
    cmpt
    #
    cT
    cS
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
    cF
    cR
    cS
    ccn
    co
    wcel
    #
    @1
    @0
    wcel
    #
    @2
    @6
    wcel
    #
    xkoco1cn.f
    cF
    @1
    cR
    cS
    cT
    cnco
    #
    sylan
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
    cF
    @15
    cima
    #
    cima
    #
    @17
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
    @23
    wa
    @24
    @39
    @43
    wb
    @38
    @22
    @23
    @24
    wph
    @22
    @36
    @27
    xkoco1cn.f
    ad2antrr
    #
    @25
    sylan
    @18
    @43
    vh
    @2
    @6
    @14
    @2
    wceq
    #
    @16
    @42
    @17
    @45
    @16
    @2
    @15
    cima
    @42
    @14
    @2
    @15
    imaeq1
    @1
    cF
    @15
    imaco
    syl6eq
    sseq1d
    elrab3
    syl
    rabbidva
    @38
    @41
    cS
    cT
    @17
    vg
    cS
    cuni
    #
    @46
    eqid
    #
    wph
    cS
    ctop
    wcel
    #
    @36
    @27
    wph
    @22
    @48
    xkoco1cn.f
    cF
    cR
    cS
    cntop2
    syl
    #
    ad2antrr
    wph
    cT
    ctop
    wcel
    #
    @36
    @27
    xkoco1cn.t
    ad2antrr
    @38
    @41
    cF
    crn
    #
    @46
    cF
    @15
    imassrn
    @38
    @22
    @11
    @46
    cF
    wf
    @51
    @46
    wss
    @44
    cF
    cR
    cS
    @11
    @46
    @31
    @47
    cnf
    @11
    @46
    cF
    frn
    3syl
    syl5ss
    @37
    @27
    @22
    cS
    @41
    crest
    co
    ccmp
    wcel
    @44
    @15
    cF
    cR
    cS
    imacmp
    sylancom
    wph
    @34
    @35
    @27
    simplrr
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
    @48
    @50
    @4
    @0
    ctopon
    cfv
    wcel
    @49
    xkoco1cn.t
    cS
    cT
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
    @52
    @20
    wf
    @21
    @52
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
    @53
    @52
    @20
    frn
    ax-mp
    ssexi
    a1i
    wph
    cR
    ctop
    wcel
    #
    @50
    @5
    @21
    cfi
    cfv
    ctg
    cfv
    wceq
    wph
    @22
    @54
    xkoco1cn.f
    cF
    cR
    cS
    cntop1
    syl
    #
    xkoco1cn.t
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
    @54
    @50
    @5
    @6
    ctopon
    cfv
    wcel
    @55
    xkoco1cn.t
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
