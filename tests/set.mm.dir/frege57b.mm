include "weq.mm"
include "wsb.mm"
include "wi.mm"
include "frege52b.mm"
include "frege56b.mm"
include "ax-mp.mm"

theorem frege57b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> ( [ y / z ] ph -> [ x / z ] ph ) )

  proof
    vy
    vx
    weq
    wph
    vz
    vy
    wsb
    wph
    vz
    vx
    wsb
    wi
    #
    wi
    vx
    vy
    weq
    @0
    wi
    wph
    vy
    vx
    vz
    frege52b
    wph
    vy
    vx
    vz
    frege56b
    ax-mp
end
