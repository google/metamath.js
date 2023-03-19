include "wss.mm"
include "cab.mm"
include "cin.mm"
include "crab.mm"
include "wceq.mm"
include "df-ss.mm"
include "ineq1.mm"
include "eqcomd.mm"
include "sylbi.mm"
include "dfrab3.mm"
include "ineq2i.mm"
include "inass.mm"
include "eqtr4i.mm"
include "3eqtr4g.mm"

theorem dfrab3ss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> { x e. A | ph } = ( A i^i { x e. B | ph } ) )

  proof
    cA
    cB
    wss
    #
    cA
    wph
    vx
    cab
    #
    cin
    #
    cA
    cB
    cin
    #
    @1
    cin
    #
    wph
    vx
    cA
    crab
    cA
    wph
    vx
    cB
    crab
    #
    cin
    #
    @0
    @3
    cA
    wceq
    #
    @2
    @4
    wceq
    cA
    cB
    df-ss
    @7
    @4
    @2
    @3
    cA
    @1
    ineq1
    eqcomd
    sylbi
    wph
    vx
    cA
    dfrab3
    @6
    cA
    cB
    @1
    cin
    #
    cin
    @4
    @5
    @8
    cA
    wph
    vx
    cB
    dfrab3
    ineq2i
    cA
    cB
    @1
    inass
    eqtr4i
    3eqtr4g
end
