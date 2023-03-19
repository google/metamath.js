include "wsb.mm"
include "wi.mm"
include "wal.mm"
include "frege62b.mm"
include "frege24.mm"
include "ax-mp.mm"

theorem frege63b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ x / y ] ph -> ( ps -> ( A. y ( ph -> ch ) -> [ x / y ] ch ) ) )

  proof
    wph
    vy
    vx
    wsb
    #
    wph
    wch
    wi
    vy
    wal
    wch
    vy
    vx
    wsb
    wi
    #
    wi
    @0
    wps
    @1
    wi
    wi
    wph
    wch
    vx
    vy
    frege62b
    @0
    @1
    wps
    frege24
    ax-mp
end
