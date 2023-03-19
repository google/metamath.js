include "cmpt.mm"
include "cres.mm"
include "clo1.mm"
include "resmptd.mm"
include "wcel.mm"
include "lo1res.mm"
include "syl.mm"
include "eqeltrrd.mm"

theorem lo1res2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume rlimres2.1: |- ( ph -> A C_ B )
  assume lo1res2.2: |- ( ph -> ( x e. B |-> C ) e. <_O(1) )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( x e. A |-> C ) e. <_O(1) )

  proof
    wph
    vx
    cB
    cC
    cmpt
    #
    cA
    cres
    #
    vx
    cA
    cC
    cmpt
    clo1
    wph
    vx
    cB
    cA
    cC
    rlimres2.1
    resmptd
    wph
    @0
    clo1
    wcel
    @1
    clo1
    wcel
    lo1res2.2
    cA
    @0
    lo1res
    syl
    eqeltrrd
end
