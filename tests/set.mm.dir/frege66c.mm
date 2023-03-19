include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "frege65c.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege66c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume frege59c.a: |- A e. B


  assert |- ( A. x ( ph -> ps ) -> ( A. x ( ch -> ph ) -> ( [. A / x ]. ch -> [. A / x ]. ps ) ) )

  proof
    wch
    wph
    wi
    vx
    wal
    #
    wph
    wps
    wi
    vx
    wal
    #
    wch
    vx
    cA
    wsbc
    wps
    vx
    cA
    wsbc
    wi
    #
    wi
    wi
    @1
    @0
    @2
    wi
    wi
    wch
    wph
    wps
    vx
    cA
    cB
    frege59c.a
    frege65c
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
