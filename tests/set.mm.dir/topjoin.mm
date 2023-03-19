include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "csn.mm"
include "cuni.mm"
include "cun.mm"
include "cfi.mm"
include "ctg.mm"
include "cv.mm"
include "wral.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "ctop.mm"
include "topontop.mm"
include "ad2antrl.mm"
include "toponmax.mm"
include "snssd.mm"
include "simprr.mm"
include "unissb.mm"
include "sylibr.mm"
include "unssd.mm"
include "tgfiss.mm"
include "syl2anc.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ssintrab.mm"
include "ctb.mm"
include "fibas.mm"
include "tgtopon.mm"
include "ax-mp.mm"
include "uniun.mm"
include "wceq.mm"
include "unisng.mm"
include "adantr.mm"
include "uneq1d.mm"
include "syl5req.mm"
include "cpw.mm"
include "simpr.mm"
include "toponuni.mm"
include "eqimss2.mm"
include "syl.mm"
include "sspwuni.mm"
include "selpw.mm"
include "ssriv.mm"
include "syl6ss.mm"
include "sylib.mm"
include "ssequn2.mm"
include "cvv.mm"
include "snex.mm"
include "fvex.mm"
include "ssex.mm"
include "adantl.mm"
include "uniexg.mm"
include "unexg.mm"
include "sylancr.mm"
include "fiuni.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "syl5eleqr.mm"
include "elssuni.mm"
include "ssun2.mm"
include "ssfii.mm"
include "sylan9ssr.mm"
include "bastg.mm"
include "sseq2.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "intss1.mm"
include "eqssd.mm"

theorem topjoin
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cV: class V
  let cX: class X
  let vt: setvar t
  let vy: setvar y
  let cA: class A
  let vx: setvar x
  let cT: class T

  disjoint j k
  disjoint S j
  disjoint S k
  disjoint V j
  disjoint V k
  disjoint X j
  disjoint X k
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint t x
  disjoint S t
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint V t
  disjoint V x
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint T t
  disjoint T x
  assert |- ( ( X e. V /\ S C_ ( TopOn ` X ) ) -> ( topGen ` ( fi ` ( { X } u. U. S ) ) ) = |^| { k e. ( TopOn ` X ) | A. j e. S j C_ k } )

  proof
    cX
    cV
    wcel
    #
    cS
    cX
    ctopon
    cfv
    #
    wss
    #
    wa
    #
    cX
    csn
    #
    cS
    cuni
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    vj
    cv
    #
    vk
    cv
    #
    wss
    #
    vj
    cS
    wral
    #
    vk
    @1
    crab
    #
    cint
    #
    @3
    @12
    @8
    @10
    wss
    #
    wi
    #
    vk
    @1
    wral
    @8
    @14
    wss
    @3
    @16
    vk
    @1
    @3
    @10
    @1
    wcel
    #
    @12
    @15
    @3
    @17
    @12
    wa
    wa
    #
    @10
    ctop
    wcel
    #
    @6
    @10
    wss
    @15
    @17
    @19
    @3
    @12
    cX
    @10
    topontop
    ad2antrl
    @18
    @4
    @5
    @10
    @18
    cX
    @10
    @17
    cX
    @10
    wcel
    @3
    @12
    cX
    @10
    toponmax
    ad2antrl
    snssd
    @18
    @12
    @5
    @10
    wss
    @3
    @17
    @12
    simprr
    vj
    cS
    @10
    unissb
    sylibr
    unssd
    @6
    @10
    tgfiss
    syl2anc
    expr
    ralrimiva
    @12
    vk
    @8
    @1
    ssintrab
    sylibr
    @3
    @8
    @13
    wcel
    #
    @14
    @8
    wss
    @3
    @8
    @1
    wcel
    @9
    @8
    wss
    #
    vj
    cS
    wral
    #
    @20
    @3
    @8
    @7
    cuni
    #
    ctopon
    cfv
    #
    @1
    @7
    ctb
    wcel
    #
    @8
    @24
    wcel
    @6
    fibas
    #
    @7
    tgtopon
    ax-mp
    @3
    cX
    @23
    ctopon
    @3
    cX
    @5
    cuni
    #
    cun
    #
    @6
    cuni
    #
    cX
    @23
    @3
    @29
    @4
    cuni
    #
    @27
    cun
    @28
    @4
    @5
    uniun
    @3
    @30
    cX
    @27
    @0
    @30
    cX
    wceq
    @2
    cX
    cV
    unisng
    adantr
    uneq1d
    syl5req
    @3
    @27
    cX
    wss
    #
    @28
    cX
    wceq
    @3
    @5
    cX
    cpw
    #
    wss
    #
    @31
    @3
    cS
    @32
    cpw
    #
    wss
    @33
    @3
    cS
    @1
    @34
    @0
    @2
    simpr
    vk
    @1
    @34
    @17
    @10
    @32
    wss
    #
    @10
    @34
    wcel
    @17
    @10
    cuni
    #
    cX
    wss
    #
    @35
    @17
    cX
    @36
    wceq
    @37
    cX
    @10
    toponuni
    @36
    cX
    eqimss2
    syl
    @10
    cX
    sspwuni
    sylibr
    vk
    @32
    selpw
    sylibr
    ssriv
    syl6ss
    cS
    @32
    sspwuni
    sylib
    @5
    cX
    sspwuni
    sylib
    @27
    cX
    ssequn2
    sylib
    @3
    @6
    cvv
    wcel
    #
    @29
    @23
    wceq
    @3
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    #
    @38
    cX
    snex
    @3
    cS
    cvv
    wcel
    #
    @39
    @2
    @40
    @0
    cS
    @1
    cX
    ctopon
    fvex
    ssex
    adantl
    cS
    cvv
    uniexg
    syl
    @4
    @5
    cvv
    cvv
    unexg
    sylancr
    #
    @6
    cvv
    fiuni
    syl
    3eqtr3d
    fveq2d
    syl5eleqr
    @3
    @21
    vj
    cS
    @3
    @9
    cS
    wcel
    #
    wa
    @9
    @7
    @8
    @42
    @3
    @9
    @6
    @7
    @42
    @9
    @5
    @6
    @9
    cS
    elssuni
    @5
    @4
    ssun2
    syl6ss
    @3
    @38
    @6
    @7
    wss
    @41
    @6
    cvv
    ssfii
    syl
    sylan9ssr
    @25
    @7
    @8
    wss
    @26
    @7
    ctb
    bastg
    ax-mp
    syl6ss
    ralrimiva
    @12
    @22
    vk
    @8
    @1
    @10
    @8
    wceq
    @11
    @21
    vj
    cS
    @10
    @8
    @9
    sseq2
    ralbidv
    elrab
    sylanbrc
    @8
    @13
    intss1
    syl
    eqssd
end
