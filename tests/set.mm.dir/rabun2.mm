include "cun.mm"
include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "uneq12i.mm"
include "wo.mm"
include "elun.mm"
include "anbi1i.mm"
include "andir.mm"
include "bitri.mm"
include "abbii.mm"
include "unab.mm"
include "eqtr4i.mm"

theorem rabun2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- { x e. ( A u. B ) | ph } = ( { x e. A | ph } u. { x e. B | ph } )

  proof
    wph
    vx
    cA
    cB
    cun
    #
    crab
    vx
    cv
    #
    @0
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    wph
    vx
    cA
    crab
    #
    wph
    vx
    cB
    crab
    #
    cun
    #
    wph
    vx
    @0
    df-rab
    @7
    @1
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
    wph
    wa
    #
    vx
    cab
    #
    cun
    #
    @4
    @5
    @10
    @6
    @13
    wph
    vx
    cA
    df-rab
    wph
    vx
    cB
    df-rab
    uneq12i
    @4
    @9
    @12
    wo
    #
    vx
    cab
    @14
    @3
    @15
    vx
    @3
    @8
    @11
    wo
    #
    wph
    wa
    @15
    @2
    @16
    wph
    @1
    cA
    cB
    elun
    anbi1i
    @8
    @11
    wph
    andir
    bitri
    abbii
    @9
    @12
    vx
    unab
    eqtr4i
    eqtr4i
    eqtr4i
end
