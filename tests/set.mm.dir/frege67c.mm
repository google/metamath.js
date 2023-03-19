include "wal.mm"
include "wsbc.mm"
include "wi.mm"
include "wb.mm"
include "frege58c.mm"
include "frege7.mm"
include "ax-mp.mm"

theorem frege67c
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume frege59c.a: |- A e. B


  assert |- ( ( ( A. x ph <-> ps ) -> ( ps -> A. x ph ) ) -> ( ( A. x ph <-> ps ) -> ( ps -> [. A / x ]. ph ) ) )

  proof
    wph
    vx
    wal
    #
    wph
    vx
    cA
    wsbc
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
    cA
    cB
    frege59c.a
    frege58c
    @0
    @1
    @2
    wps
    frege7
    ax-mp
end
