include "wal.mm"
include "wsb.mm"
include "wi.mm"
include "ax-frege58b.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege61b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( [ x / y ] ph -> ps ) -> ( A. y ph -> ps ) )

  proof
    wph
    vy
    wal
    #
    wph
    vy
    vx
    wsb
    #
    wi
    @1
    wps
    wi
    @0
    wps
    wi
    wi
    wph
    vy
    vx
    ax-frege58b
    @0
    @1
    wps
    frege9
    ax-mp
end
