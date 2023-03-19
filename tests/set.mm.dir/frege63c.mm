include "wsbc.mm"
include "wi.mm"
include "wal.mm"
include "frege62c.mm"
include "frege24.mm"
include "ax-mp.mm"

theorem frege63c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume frege59c.a: |- A e. B


  assert |- ( [. A / x ]. ph -> ( ps -> ( A. x ( ph -> ch ) -> [. A / x ]. ch ) ) )

  proof
    wph
    vx
    cA
    wsbc
    #
    wph
    wch
    wi
    vx
    wal
    wch
    vx
    cA
    wsbc
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
    cA
    cB
    frege59c.a
    frege62c
    @0
    @1
    wps
    frege24
    ax-mp
end
