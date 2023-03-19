include "weq.mm"
include "wsb.mm"
include "wi.mm"
include "frege54cor1b.mm"
include "frege53b.mm"
include "ax-mp.mm"

theorem frege55lem2b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> [ y / z ] z = x )

  proof
    vz
    vx
    weq
    #
    vz
    vx
    wsb
    vx
    vy
    weq
    @0
    vz
    vy
    wsb
    wi
    vx
    vz
    frege54cor1b
    @0
    vx
    vz
    vy
    frege53b
    ax-mp
end
