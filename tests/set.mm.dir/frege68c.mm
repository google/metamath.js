include "wal.mm"
include "wb.mm"
include "wi.mm"
include "wsbc.mm"
include "frege57aid.mm"
include "frege67c.mm"
include "ax-mp.mm"

theorem frege68c
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume frege59c.a: |- A e. B


  assert |- ( ( A. x ph <-> ps ) -> ( ps -> [. A / x ]. ph ) )

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
    cA
    wsbc
    wi
    wi
    @0
    wps
    frege57aid
    wph
    wps
    vx
    cA
    cB
    frege59c.a
    frege67c
    ax-mp
end
