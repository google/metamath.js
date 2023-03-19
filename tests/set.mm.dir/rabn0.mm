include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "rabeq0.mm"
include "necon3abii.mm"
include "dfrex2.mm"
include "bitr4i.mm"

theorem rabn0
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } =/= (/) <-> E. x e. A ph )

  proof
    wph
    vx
    cA
    crab
    #
    c0
    wne
    wph
    wn
    vx
    cA
    wral
    #
    wn
    wph
    vx
    cA
    wrex
    @1
    @0
    c0
    wph
    vx
    cA
    rabeq0
    necon3abii
    wph
    vx
    cA
    dfrex2
    bitr4i
end
