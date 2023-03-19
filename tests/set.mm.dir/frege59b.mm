include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "wn.mm"
include "frege58bcor.mm"
include "frege30.mm"
include "ax-mp.mm"

theorem frege59b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ x / y ] ph -> ( -. [ x / y ] ps -> -. A. y ( ph -> ps ) ) )

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
    @2
    wn
    @0
    wn
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
    frege30
    ax-mp
end
