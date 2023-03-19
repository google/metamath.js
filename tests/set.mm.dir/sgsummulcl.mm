include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "srgcmn.mm"
include "syl.mm"
include "cmnd.mm"
include "srgmnd.mm"
include "cmhm.mm"
include "srglmhm.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "gsummhm2.mm"

theorem sgsummulcl
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
  assume srgsummulcr.b: |- B = ( Base ` R )
  assume srgsummulcr.z: |- .0. = ( 0g ` R )
  assume srgsummulcr.p: |- .+ = ( +g ` R )
  assume srgsummulcr.t: |- .x. = ( .r ` R )
  assume srgsummulcr.r: |- ( ph -> R e. SRing )
  assume srgsummulcr.a: |- ( ph -> A e. V )
  assume srgsummulcr.y: |- ( ph -> Y e. B )
  assume srgsummulcr.x: |- ( ( ph /\ k e. A ) -> X e. B )
  assume srgsummulcr.n: |- ( ph -> ( k e. A |-> X ) finSupp .0. )

  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint .x. k
  disjoint Y k
  disjoint k x
  disjoint A x
  disjoint B x
  disjoint .x. x
  disjoint R x
  disjoint X x
  disjoint Y x
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
    srgsummulcr.b
    srgsummulcr.z
    wph
    cR
    csrg
    wcel
    #
    cR
    ccmn
    wcel
    srgsummulcr.r
    cR
    srgcmn
    syl
    wph
    @3
    cR
    cmnd
    wcel
    srgsummulcr.r
    cR
    srgmnd
    syl
    srgsummulcr.a
    wph
    @3
    cY
    cB
    wcel
    vx
    cB
    @1
    cmpt
    cR
    cR
    cmhm
    co
    wcel
    srgsummulcr.r
    srgsummulcr.y
    vx
    cB
    cR
    c.x
    cY
    srgsummulcr.b
    srgsummulcr.t
    srglmhm
    syl2anc
    srgsummulcr.x
    srgsummulcr.n
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
