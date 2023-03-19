include "cfn.mm"
include "wcel.mm"
include "crab.mm"
include "cab.mm"
include "cin.mm"
include "dfrab3.mm"
include "infi.mm"
include "syl5eqel.mm"

theorem rabfi
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. Fin -> { x e. A | ph } e. Fin )

  proof
    cA
    cfn
    wcel
    wph
    vx
    cA
    crab
    cA
    wph
    vx
    cab
    #
    cin
    cfn
    wph
    vx
    cA
    dfrab3
    cA
    @0
    infi
    syl5eqel
end
