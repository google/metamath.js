include "crab.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "ssdif0.mm"
include "ssrabeq.mm"
include "bitr3i.mm"

theorem difrab0eq
  let wph: wff ph
  let vx: setvar x
  let cV: class V

  disjoint V x
  assert |- ( ( V \ { x e. V | ph } ) = (/) <-> V = { x e. V | ph } )

  proof
    cV
    wph
    vx
    cV
    crab
    #
    cdif
    c0
    wceq
    cV
    @0
    wss
    cV
    @0
    wceq
    cV
    @0
    ssdif0
    wph
    vx
    cV
    ssrabeq
    bitr3i
end
