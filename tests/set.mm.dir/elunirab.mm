include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "cuni.mm"
include "wex.mm"
include "crab.mm"
include "wrex.mm"
include "eluniab.mm"
include "df-rab.mm"
include "unieqi.mm"
include "eleq2i.mm"
include "df-rex.mm"
include "an12.mm"
include "exbii.mm"
include "bitri.mm"
include "3bitr4i.mm"

theorem elunirab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A e. U. { x e. B | ph } <-> E. x e. B ( A e. x /\ ph ) )

  proof
    cA
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    cuni
    #
    wcel
    cA
    @0
    wcel
    #
    @2
    wa
    #
    vx
    wex
    #
    cA
    wph
    vx
    cB
    crab
    #
    cuni
    #
    wcel
    @5
    wph
    wa
    #
    vx
    cB
    wrex
    #
    @2
    vx
    cA
    eluniab
    @9
    @4
    cA
    @8
    @3
    wph
    vx
    cB
    df-rab
    unieqi
    eleq2i
    @11
    @1
    @10
    wa
    #
    vx
    wex
    @7
    @10
    vx
    cB
    df-rex
    @12
    @6
    vx
    @1
    @5
    wph
    an12
    exbii
    bitri
    3bitr4i
end
