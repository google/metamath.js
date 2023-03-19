include "weq.mm"
include "wsb.mm"
include "wi.mm"
include "frege52b.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege53b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( [ x / y ] ph -> ( x = z -> [ z / y ] ph ) )

  proof
    vx
    vz
    weq
    #
    wph
    vy
    vx
    wsb
    #
    wph
    vy
    vz
    wsb
    #
    wi
    wi
    @1
    @0
    @2
    wi
    wi
    wph
    vx
    vz
    vy
    frege52b
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
