include "wal.mm"
include "wsbc.mm"
include "wi.mm"
include "frege58c.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege61c
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume frege59c.a: |- A e. B


  assert |- ( ( [. A / x ]. ph -> ps ) -> ( A. x ph -> ps ) )

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
    @1
    wps
    wi
    @0
    wps
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
    wps
    frege9
    ax-mp
end
