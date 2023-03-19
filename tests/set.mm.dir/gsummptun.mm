include "cun.mm"
include "eqidd.mm"
include "gsummptfidmsplit.mm"

theorem gsummptun
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cW: class W
  let c.0: class .0.
  assume gsummptun.b: |- B = ( Base ` W )
  assume gsummptun.z: |- .0. = ( 0g ` W )
  assume gsummptun.p: |- .+ = ( +g ` W )
  assume gsummptun.w: |- ( ph -> W e. CMnd )
  assume gsummptun.a: |- ( ph -> ( A u. C ) e. Fin )
  assume gsummptun.d: |- ( ph -> ( A i^i C ) = (/) )
  assume gsummptun.1: |- ( ( ph /\ x e. ( A u. C ) ) -> D e. B )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> ( W gsum ( x e. ( A u. C ) |-> D ) ) = ( ( W gsum ( x e. A |-> D ) ) .+ ( W gsum ( x e. C |-> D ) ) ) )

  proof
    wph
    cA
    cC
    cun
    #
    cB
    cA
    cC
    c.pl
    vx
    cW
    cD
    gsummptun.b
    gsummptun.p
    gsummptun.w
    gsummptun.a
    gsummptun.1
    gsummptun.d
    wph
    @0
    eqidd
    gsummptfidmsplit
end
