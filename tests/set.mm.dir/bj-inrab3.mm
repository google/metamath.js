include "crab.mm"
include "cin.mm"
include "cab.mm"
include "dfrab3.mm"
include "ineq2i.mm"
include "incom.mm"
include "in12.mm"
include "3eqtr4i.mm"
include "eqtr4i.mm"

theorem bj-inrab3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A i^i { x e. B | ph } ) = ( { x e. A | ph } i^i B )

  proof
    cA
    wph
    vx
    cB
    crab
    #
    cin
    cA
    cB
    wph
    vx
    cab
    #
    cin
    #
    cin
    #
    wph
    vx
    cA
    crab
    #
    cB
    cin
    #
    @0
    @2
    cA
    wph
    vx
    cB
    dfrab3
    ineq2i
    cB
    @4
    cin
    cB
    cA
    @1
    cin
    #
    cin
    @5
    @3
    @4
    @6
    cB
    wph
    vx
    cA
    dfrab3
    ineq2i
    @4
    cB
    incom
    cA
    cB
    @1
    in12
    3eqtr4i
    eqtr4i
end
