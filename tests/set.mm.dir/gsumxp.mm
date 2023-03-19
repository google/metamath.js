include "cgsu.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wrel.mm"
include "relxp.mm"
include "a1i.mm"
include "cdm.mm"
include "wss.mm"
include "dmxpss.mm"
include "gsum2d.mm"
include "wa.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "cin.mm"
include "df-res.mm"
include "inxp.mm"
include "eqtri.mm"
include "wceq.mm"
include "simpr.mm"
include "snssd.mm"
include "sseqin2.mm"
include "sylib.mm"
include "inv1.mm"
include "xpeq12d.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "c0.mm"
include "wne.mm"
include "vex.mm"
include "snnz.mm"
include "rnxp.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "mpteq1d.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem gsumxp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cU: class U
  assume gsumxp.b: |- B = ( Base ` G )
  assume gsumxp.z: |- .0. = ( 0g ` G )
  assume gsumxp.g: |- ( ph -> G e. CMnd )
  assume gsumxp.a: |- ( ph -> A e. V )
  assume gsumxp.r: |- ( ph -> C e. W )
  assume gsumxp.f: |- ( ph -> F : ( A X. C ) --> B )
  assume gsumxp.w: |- ( ph -> F finSupp .0. )

  disjoint j k
  disjoint .0. j
  disjoint .0. k
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint k ph
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint C j
  disjoint C k
  disjoint F j
  disjoint F k
  disjoint V j
  disjoint U j
  disjoint U k
  assert |- ( ph -> ( G gsum F ) = ( G gsum ( j e. A |-> ( G gsum ( k e. C |-> ( j F k ) ) ) ) ) )

  proof
    wph
    cG
    cF
    cgsu
    co
    cG
    vj
    cA
    cG
    vk
    cA
    cC
    cxp
    #
    vj
    cv
    #
    csn
    #
    cima
    #
    @1
    vk
    cv
    cF
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    cG
    vj
    cA
    cG
    vk
    cC
    @4
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    wph
    @0
    cB
    cA
    vj
    vk
    cF
    cG
    cvv
    cV
    c.0
    gsumxp.b
    gsumxp.z
    gsumxp.g
    wph
    cA
    cV
    wcel
    cC
    cW
    wcel
    @0
    cvv
    wcel
    gsumxp.a
    gsumxp.r
    cA
    cC
    cV
    cW
    xpexg
    syl2anc
    @0
    wrel
    wph
    cA
    cC
    relxp
    a1i
    gsumxp.a
    @0
    cdm
    cA
    wss
    wph
    cA
    cC
    dmxpss
    a1i
    gsumxp.f
    gsumxp.w
    gsum2d
    wph
    @7
    @10
    cG
    cgsu
    wph
    vj
    cA
    @6
    @9
    wph
    @1
    cA
    wcel
    #
    wa
    #
    @5
    @8
    cG
    cgsu
    @12
    vk
    @3
    cC
    @4
    @12
    @3
    @0
    @2
    cres
    #
    crn
    #
    cC
    @0
    @2
    df-ima
    @12
    @14
    @2
    cC
    cxp
    #
    crn
    #
    cC
    @12
    @13
    @15
    @12
    @13
    cA
    @2
    cin
    #
    cC
    cvv
    cin
    #
    cxp
    #
    @15
    @13
    @0
    @2
    cvv
    cxp
    cin
    @19
    @0
    @2
    df-res
    cA
    cC
    @2
    cvv
    inxp
    eqtri
    @12
    @17
    @2
    @18
    cC
    @12
    @2
    cA
    wss
    @17
    @2
    wceq
    @12
    @1
    cA
    wph
    @11
    simpr
    snssd
    @2
    cA
    sseqin2
    sylib
    @18
    cC
    wceq
    @12
    cC
    inv1
    a1i
    xpeq12d
    syl5eq
    rneqd
    @2
    c0
    wne
    @16
    cC
    wceq
    @1
    vj
    vex
    snnz
    @2
    cC
    rnxp
    ax-mp
    syl6eq
    syl5eq
    mpteq1d
    oveq2d
    mpteq2dva
    oveq2d
    eqtrd
end
