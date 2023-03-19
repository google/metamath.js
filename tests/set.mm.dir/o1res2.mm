include "cmpt.mm"
include "cres.mm"
include "co1.mm"
include "resmptd.mm"
include "wcel.mm"
include "o1res.mm"
include "syl.mm"
include "eqeltrrd.mm"

theorem o1res2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume rlimres2.1: |- ( ph -> A C_ B )
  assume o1res2.2: |- ( ph -> ( x e. B |-> C ) e. O(1) )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( x e. A |-> C ) e. O(1) )

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
    co1
    wph
    vx
    cB
    cA
    cC
    rlimres2.1
    resmptd
    wph
    @0
    co1
    wcel
    @1
    co1
    wcel
    o1res2.2
    cA
    @0
    o1res
    syl
    eqeltrrd
end
