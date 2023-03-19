include "crab.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "abid1.mm"
include "ineq12i.mm"
include "inab.mm"
include "elin.mm"
include "anbi1i.mm"
include "an32.mm"
include "bitri.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem inrab2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint B x
  assert |- ( { x e. A | ph } i^i B ) = { x e. ( A i^i B ) | ph }

  proof
    wph
    vx
    cA
    crab
    #
    cB
    cin
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @1
    cB
    wcel
    #
    vx
    cab
    #
    cin
    #
    wph
    vx
    cA
    cB
    cin
    #
    crab
    #
    @0
    @4
    cB
    @6
    wph
    vx
    cA
    df-rab
    vx
    cB
    abid1
    ineq12i
    @9
    @1
    @8
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @7
    wph
    vx
    @8
    df-rab
    @7
    @3
    @5
    wa
    #
    vx
    cab
    @12
    @3
    @5
    vx
    inab
    @11
    @13
    vx
    @11
    @2
    @5
    wa
    #
    wph
    wa
    @13
    @10
    @14
    wph
    @1
    cA
    cB
    elin
    anbi1i
    @2
    @5
    wph
    an32
    bitri
    abbii
    eqtr4i
    eqtr4i
    eqtr4i
end
