include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "clmod.mm"
include "wcel.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "syl.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "cghm.mm"
include "cmhm.mm"
include "lmodvsghm.mm"
include "syl2anc.mm"
include "ghmmhm.mm"
include "oveq2.mm"
include "gsummhm2.mm"

theorem gsumvsmul
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vy: setvar y
  assume gsumvsmul.b: |- B = ( Base ` R )
  assume gsumvsmul.s: |- S = ( Scalar ` R )
  assume gsumvsmul.k: |- K = ( Base ` S )
  assume gsumvsmul.z: |- .0. = ( 0g ` R )
  assume gsumvsmul.p: |- .+ = ( +g ` R )
  assume gsumvsmul.t: |- .x. = ( .s ` R )
  assume gsumvsmul.r: |- ( ph -> R e. LMod )
  assume gsumvsmul.a: |- ( ph -> A e. V )
  assume gsumvsmul.x: |- ( ph -> X e. K )
  assume gsumvsmul.y: |- ( ( ph /\ k e. A ) -> Y e. B )
  assume gsumvsmul.n: |- ( ph -> ( k e. A |-> Y ) finSupp .0. )

  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint .x. k
  disjoint S k
  disjoint K k
  disjoint X k
  disjoint .0. k
  disjoint A y
  disjoint k y
  disjoint B y
  disjoint ph y
  disjoint .x. y
  disjoint Y y
  disjoint S y
  disjoint K y
  disjoint X y
  disjoint .0. y
  disjoint R y
  assert |- ( ph -> ( R gsum ( k e. A |-> ( X .x. Y ) ) ) = ( X .x. ( R gsum ( k e. A |-> Y ) ) ) )

  proof
    wph
    vy
    cA
    cB
    cX
    vy
    cv
    #
    c.x
    co
    #
    cX
    cY
    c.x
    co
    vk
    cX
    cR
    vk
    cA
    cY
    cmpt
    cgsu
    co
    #
    c.x
    co
    cR
    cR
    cV
    cY
    c.0
    gsumvsmul.b
    gsumvsmul.z
    wph
    cR
    clmod
    wcel
    #
    cR
    ccmn
    wcel
    #
    gsumvsmul.r
    cR
    lmodcmn
    syl
    #
    wph
    @4
    cR
    cmnd
    wcel
    @5
    cR
    cmnmnd
    syl
    gsumvsmul.a
    wph
    vy
    cB
    @1
    cmpt
    #
    cR
    cR
    cghm
    co
    wcel
    #
    @6
    cR
    cR
    cmhm
    co
    wcel
    wph
    @3
    cX
    cK
    wcel
    @7
    gsumvsmul.r
    gsumvsmul.x
    vy
    cX
    c.x
    cS
    cK
    cB
    cR
    gsumvsmul.b
    gsumvsmul.s
    gsumvsmul.t
    gsumvsmul.k
    lmodvsghm
    syl2anc
    cR
    cR
    @6
    ghmmhm
    syl
    gsumvsmul.y
    gsumvsmul.n
    @0
    cY
    cX
    c.x
    oveq2
    @0
    @2
    cX
    c.x
    oveq2
    gsummhm2
end
