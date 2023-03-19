include "wi.mm"
include "wsbc.mm"
include "wal.mm"
include "sbcim1.mm"
include "frege64c.mm"
include "syl.mm"
include "frege61c.mm"
include "ax-mp.mm"

theorem frege65c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume frege59c.a: |- A e. B


  assert |- ( A. x ( ph -> ps ) -> ( A. x ( ps -> ch ) -> ( [. A / x ]. ph -> [. A / x ]. ch ) ) )

  proof
    wph
    wps
    wi
    #
    vx
    cA
    wsbc
    #
    wps
    wch
    wi
    vx
    wal
    wph
    vx
    cA
    wsbc
    #
    wch
    vx
    cA
    wsbc
    wi
    wi
    #
    wi
    @0
    vx
    wal
    @3
    wi
    @1
    @2
    wps
    vx
    cA
    wsbc
    wi
    @3
    wph
    wps
    vx
    cA
    sbcim1
    wph
    wps
    wch
    vx
    cA
    cB
    cA
    frege59c.a
    frege64c
    syl
    @0
    @3
    vx
    cA
    cB
    frege59c.a
    frege61c
    ax-mp
end
