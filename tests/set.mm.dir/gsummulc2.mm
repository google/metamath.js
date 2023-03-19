include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crg.mm"
include "wcel.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "syl.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "cghm.mm"
include "cmhm.mm"
include "ringlghm.mm"
include "syl2anc.mm"
include "ghmmhm.mm"
include "oveq2.mm"
include "gsummhm2.mm"

theorem gsummulc2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let vk: setvar k
  let cV: class V
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  assume gsummulc1.b: |- B = ( Base ` R )
  assume gsummulc1.z: |- .0. = ( 0g ` R )
  assume gsummulc1.p: |- .+ = ( +g ` R )
  assume gsummulc1.t: |- .x. = ( .r ` R )
  assume gsummulc1.r: |- ( ph -> R e. Ring )
  assume gsummulc1.a: |- ( ph -> A e. V )
  assume gsummulc1.y: |- ( ph -> Y e. B )
  assume gsummulc1.x: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsummulc1.n: |- ( ph -> ( k e. A |-> X ) finSupp .0. )

  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint .x. k
  disjoint Y k
  disjoint k x
  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint .x. x
  disjoint R x
  disjoint X x
  disjoint Y x
  disjoint .0. x
  assert |- ( ph -> ( R gsum ( k e. A |-> ( Y .x. X ) ) ) = ( Y .x. ( R gsum ( k e. A |-> X ) ) ) )

  proof
    wph
    vx
    cA
    cB
    cY
    vx
    cv
    #
    c.x
    co
    #
    cY
    cX
    c.x
    co
    vk
    cY
    cR
    vk
    cA
    cX
    cmpt
    cgsu
    co
    #
    c.x
    co
    cR
    cR
    cV
    cX
    c.0
    gsummulc1.b
    gsummulc1.z
    wph
    cR
    crg
    wcel
    #
    cR
    ccmn
    wcel
    gsummulc1.r
    cR
    ringcmn
    syl
    wph
    @3
    cR
    cmnd
    wcel
    gsummulc1.r
    cR
    ringmnd
    syl
    gsummulc1.a
    wph
    vx
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
    @4
    cR
    cR
    cmhm
    co
    wcel
    wph
    @3
    cY
    cB
    wcel
    @5
    gsummulc1.r
    gsummulc1.y
    vx
    cB
    cR
    c.x
    cY
    gsummulc1.b
    gsummulc1.t
    ringlghm
    syl2anc
    cR
    cR
    @4
    ghmmhm
    syl
    gsummulc1.x
    gsummulc1.n
    @0
    cX
    cY
    c.x
    oveq2
    @0
    @2
    cY
    c.x
    oveq2
    gsummhm2
end
