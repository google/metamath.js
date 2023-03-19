include "wi.mm"
include "wex.mm"
include "wn.mm"
include "wo.mm"
include "orc.mm"
include "eximii.mm"
include "eximp-surprise.mm"
include "mpbir.mm"

theorem eximp-surprise2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vk: setvar k
  assume eximp-surprise2.1: |- E. x -. ph


  assert |- E. x ( ph -> ps )

  proof
    wph
    wps
    wi
    vx
    wex
    wph
    wn
    #
    wps
    wo
    #
    vx
    wex
    @0
    @1
    vx
    eximp-surprise2.1
    @0
    wps
    orc
    eximii
    wph
    wps
    vx
    eximp-surprise
    mpbir
end
