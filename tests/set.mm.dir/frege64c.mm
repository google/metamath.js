include "wsbc.mm"
include "wi.mm"
include "wal.mm"
include "frege62c.mm"
include "frege18.mm"
include "ax-mp.mm"

theorem frege64c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume frege59c.a: |- A e. B


  assert |- ( ( [. C / x ]. ph -> [. A / x ]. ps ) -> ( A. x ( ps -> ch ) -> ( [. C / x ]. ph -> [. A / x ]. ch ) ) )

  proof
    wps
    vx
    cA
    wsbc
    #
    wps
    wch
    wi
    vx
    wal
    #
    wch
    vx
    cA
    wsbc
    #
    wi
    wi
    wph
    vx
    cC
    wsbc
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
    vx
    cA
    cB
    frege59c.a
    frege62c
    @0
    @1
    @2
    @3
    frege18
    ax-mp
end
