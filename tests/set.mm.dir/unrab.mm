include "crab.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wo.mm"
include "df-rab.mm"
include "uneq12i.mm"
include "unab.mm"
include "andi.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem unrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } u. { x e. A | ps } ) = { x e. A | ( ph \/ ps ) }

  proof
    wph
    vx
    cA
    crab
    #
    wps
    vx
    cA
    crab
    #
    cun
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @2
    wps
    wa
    #
    vx
    cab
    #
    cun
    #
    wph
    wps
    wo
    #
    vx
    cA
    crab
    #
    @0
    @4
    @1
    @6
    wph
    vx
    cA
    df-rab
    wps
    vx
    cA
    df-rab
    uneq12i
    @9
    @2
    @8
    wa
    #
    vx
    cab
    #
    @7
    @8
    vx
    cA
    df-rab
    @7
    @3
    @5
    wo
    #
    vx
    cab
    @11
    @3
    @5
    vx
    unab
    @10
    @12
    vx
    @2
    wph
    wps
    andi
    abbii
    eqtr4i
    eqtr4i
    eqtr4i
end
