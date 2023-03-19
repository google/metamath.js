include "wal.mm"
include "wb.mm"
include "wi.mm"
include "wsb.mm"
include "frege57aid.mm"
include "frege67b.mm"
include "ax-mp.mm"

theorem frege68b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A. x ph <-> ps ) -> ( ps -> [ y / x ] ph ) )

  proof
    wph
    vx
    wal
    #
    wps
    wb
    #
    wps
    @0
    wi
    wi
    @1
    wps
    wph
    vx
    vy
    wsb
    wi
    wi
    @0
    wps
    frege57aid
    wph
    wps
    vx
    vy
    frege67b
    ax-mp
end
