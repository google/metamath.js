include "cabl.mm"
include "wcel.mm"
include "ccmn.mm"
include "ablcmn.mm"
include "syl.mm"
include "cn0.mm"
include "orcd.mm"
include "gsummulglem.mm"

theorem gsummulgz
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  assume gsummulg.b: |- B = ( Base ` G )
  assume gsummulg.z: |- .0. = ( 0g ` G )
  assume gsummulg.t: |- .x. = ( .g ` G )
  assume gsummulg.a: |- ( ph -> A e. V )
  assume gsummulg.f: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsummulg.w: |- ( ph -> ( k e. A |-> X ) finSupp .0. )
  assume gsummulgz.g: |- ( ph -> G e. Abel )
  assume gsummulgz.n: |- ( ph -> N e. ZZ )

  disjoint A k
  disjoint B k
  disjoint N k
  disjoint k ph
  disjoint .x. k
  disjoint k x
  disjoint A x
  disjoint B x
  disjoint G x
  disjoint N x
  disjoint .x. x
  disjoint X x
  assert |- ( ph -> ( G gsum ( k e. A |-> ( N .x. X ) ) ) = ( N .x. ( G gsum ( k e. A |-> X ) ) ) )

  proof
    wph
    cA
    cB
    c.x
    vk
    cG
    cN
    cV
    cX
    c.0
    gsummulg.b
    gsummulg.z
    gsummulg.t
    gsummulg.a
    gsummulg.f
    gsummulg.w
    wph
    cG
    cabl
    wcel
    #
    cG
    ccmn
    wcel
    gsummulgz.g
    cG
    ablcmn
    syl
    gsummulgz.n
    wph
    @0
    cN
    cn0
    wcel
    gsummulgz.g
    orcd
    gsummulglem
end
