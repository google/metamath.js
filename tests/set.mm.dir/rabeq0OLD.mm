include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "crab.mm"
include "c0.mm"
include "wceq.mm"
include "ralnex.mm"
include "rabn0OLD.mm"
include "necon1bbii.mm"
include "bitr2i.mm"

theorem rabeq0OLD
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } = (/) <-> A. x e. A -. ph )

  proof
    wph
    wn
    vx
    cA
    wral
    wph
    vx
    cA
    wrex
    #
    wn
    wph
    vx
    cA
    crab
    #
    c0
    wceq
    wph
    vx
    cA
    ralnex
    @0
    @1
    c0
    wph
    vx
    cA
    rabn0OLD
    necon1bbii
    bitr2i
end
