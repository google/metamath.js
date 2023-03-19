include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "ax-frege58b.mm"
include "sbim.mm"
include "sylib.mm"

theorem frege58bcor
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    @0
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    wps
    vx
    vy
    wsb
    wi
    @0
    vx
    vy
    ax-frege58b
    wph
    wps
    vx
    vy
    sbim
    sylib
end
