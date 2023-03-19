include "wal.mm"
include "wsb.mm"
include "wi.mm"
include "wb.mm"
include "ax-frege58b.mm"
include "frege7.mm"
include "ax-mp.mm"

theorem frege67b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A. x ph <-> ps ) -> ( ps -> A. x ph ) ) -> ( ( A. x ph <-> ps ) -> ( ps -> [ y / x ] ph ) ) )

  proof
    wph
    vx
    wal
    #
    wph
    vx
    vy
    wsb
    #
    wi
    @0
    wps
    wb
    #
    wps
    @0
    wi
    wi
    @2
    wps
    @1
    wi
    wi
    wi
    wph
    vx
    vy
    ax-frege58b
    @0
    @1
    @2
    wps
    frege7
    ax-mp
end
