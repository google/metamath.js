include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "frege58bcor.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege62b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ x / y ] ph -> ( A. y ( ph -> ps ) -> [ x / y ] ps ) )

  proof
    wph
    wps
    wi
    vy
    wal
    #
    wph
    vy
    vx
    wsb
    #
    wps
    vy
    vx
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
    wps
    vy
    vx
    frege58bcor
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
