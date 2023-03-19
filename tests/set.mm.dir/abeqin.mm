include "cin.mm"
include "cab.mm"
include "crab.mm"
include "ineq1i.mm"
include "dfrab2.mm"
include "3eqtr4i.mm"

theorem abeqin
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume abeqin.1: |- A = ( B i^i C )
  assume abeqin.2: |- B = { x | ph }

  disjoint C x
  assert |- A = { x e. C | ph }

  proof
    cB
    cC
    cin
    wph
    vx
    cab
    #
    cC
    cin
    cA
    wph
    vx
    cC
    crab
    cB
    @0
    cC
    abeqin.2
    ineq1i
    abeqin.1
    wph
    vx
    cC
    dfrab2
    3eqtr4i
end
