include "wsb.mm"
include "wi.mm"
include "wal.mm"
include "frege62b.mm"
include "frege18.mm"
include "ax-mp.mm"

theorem frege64b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( [ x / y ] ph -> [ z / y ] ps ) -> ( A. y ( ps -> ch ) -> ( [ x / y ] ph -> [ z / y ] ch ) ) )

  proof
    wps
    vy
    vz
    wsb
    #
    wps
    wch
    wi
    vy
    wal
    #
    wch
    vy
    vz
    wsb
    #
    wi
    wi
    wph
    vy
    vx
    wsb
    #
    @0
    wi
    @1
    @3
    @2
    wi
    wi
    wi
    wps
    wch
    vz
    vy
    frege62b
    @0
    @1
    @2
    @3
    frege18
    ax-mp
end
