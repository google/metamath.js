include "crab.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "ssrab2.mm"
include "biantru.mm"
include "eqss.mm"
include "bitr4i.mm"

theorem ssrabeq
  let wph: wff ph
  let vx: setvar x
  let cV: class V

  disjoint V x
  assert |- ( V C_ { x e. V | ph } <-> V = { x e. V | ph } )

  proof
    cV
    wph
    vx
    cV
    crab
    #
    wss
    #
    @1
    @0
    cV
    wss
    #
    wa
    cV
    @0
    wceq
    @2
    @1
    wph
    vx
    cV
    ssrab2
    biantru
    cV
    @0
    eqss
    bitr4i
end
