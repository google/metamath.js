include "weq.mm"
include "wi.mm"
include "wsb.mm"
include "frege55b.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege56b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) -> ( y = x -> ( [ x / z ] ph -> [ y / z ] ph ) ) )

  proof
    vy
    vx
    weq
    #
    vx
    vy
    weq
    #
    wi
    @1
    wph
    vz
    vx
    wsb
    wph
    vz
    vy
    wsb
    wi
    #
    wi
    @0
    @2
    wi
    wi
    vy
    vx
    frege55b
    @0
    @1
    @2
    frege9
    ax-mp
end
