include "cv.mm"
include "csn.mm"
include "cima.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "imaexg.mm"
include "syl.mm"
include "cop.mm"
include "vex.mm"
include "elimasn.mm"
include "wa.mm"
include "cfv.mm"
include "df-ov.mm"
include "ffvelrnda.mm"
include "syl5eqel.mm"
include "sylan2b.mm"
include "eqid.mm"
include "fmptd.mm"
include "csupp.mm"
include "crn.mm"
include "cfn.mm"
include "wss.mm"
include "fsuppimpd.mm"
include "rnfi.mm"
include "cdif.mm"
include "wceq.mm"
include "wn.mm"
include "biimpi.mm"
include "opelrn.mm"
include "con3i.mm"
include "anim12i.mm"
include "eldif.mm"
include "3imtr4i.mm"
include "ssid.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "syl5eq.mm"
include "sylan2.mm"
include "suppss2.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "gsumcl2.mm"

theorem gsum2dlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gsum2d.b: |- B = ( Base ` G )
  assume gsum2d.z: |- .0. = ( 0g ` G )
  assume gsum2d.g: |- ( ph -> G e. CMnd )
  assume gsum2d.a: |- ( ph -> A e. V )
  assume gsum2d.r: |- ( ph -> Rel A )
  assume gsum2d.d: |- ( ph -> D e. W )
  assume gsum2d.s: |- ( ph -> dom A C_ D )
  assume gsum2d.f: |- ( ph -> F : A --> B )
  assume gsum2d.w: |- ( ph -> F finSupp .0. )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint F j
  disjoint F k
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint k ph
  disjoint B j
  disjoint B k
  disjoint D j
  disjoint D k
  disjoint .0. j
  disjoint .0. k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  assert |- ( ph -> ( G gsum ( k e. ( A " { j } ) |-> ( j F k ) ) ) e. B )

  proof
    wph
    cA
    vj
    cv
    #
    csn
    #
    cima
    #
    cB
    vk
    @2
    @0
    vk
    cv
    #
    cF
    co
    #
    cmpt
    #
    cG
    cvv
    c.0
    gsum2d.b
    gsum2d.z
    gsum2d.g
    wph
    cA
    cV
    wcel
    @2
    cvv
    wcel
    gsum2d.a
    cA
    @1
    cV
    imaexg
    syl
    #
    wph
    vk
    @2
    @4
    cB
    @5
    @3
    @2
    wcel
    #
    wph
    @0
    @3
    cop
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    cA
    @0
    @3
    vj
    vex
    #
    vk
    vex
    #
    elimasn
    #
    wph
    @9
    wa
    @4
    @8
    cF
    cfv
    #
    cB
    @0
    @3
    cF
    df-ov
    #
    wph
    cA
    cB
    @8
    cF
    gsum2d.f
    ffvelrnda
    syl5eqel
    sylan2b
    @5
    eqid
    fmptd
    wph
    cF
    c.0
    csupp
    co
    #
    crn
    #
    cfn
    wcel
    #
    @5
    c.0
    csupp
    co
    #
    @16
    wss
    @18
    cfn
    wcel
    wph
    @15
    cfn
    wcel
    @17
    wph
    cF
    c.0
    gsum2d.w
    fsuppimpd
    @15
    rnfi
    syl
    wph
    @2
    @4
    vk
    cvv
    @16
    c.0
    @3
    @2
    @16
    cdif
    wcel
    #
    wph
    @8
    cA
    @15
    cdif
    wcel
    #
    @4
    c.0
    wceq
    @7
    @3
    @16
    wcel
    #
    wn
    #
    wa
    @9
    @8
    @15
    wcel
    #
    wn
    #
    wa
    @19
    @20
    @7
    @9
    @22
    @24
    @7
    @9
    @12
    biimpi
    @23
    @21
    @0
    @3
    @15
    @10
    @11
    opelrn
    con3i
    anim12i
    @3
    @2
    @16
    eldif
    @8
    cA
    @15
    eldif
    3imtr4i
    wph
    @20
    wa
    @4
    @13
    c.0
    @14
    wph
    cA
    cB
    cvv
    cF
    cV
    @15
    @8
    c.0
    gsum2d.f
    @15
    @15
    wss
    wph
    @15
    ssid
    a1i
    gsum2d.a
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsum2d.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    suppssr
    syl5eq
    sylan2
    @6
    suppss2
    @16
    @18
    ssfi
    syl2anc
    gsumcl2
end
