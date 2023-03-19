include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "frege58c.mm"
include "sbcim1.mm"
include "syl6.mm"
include "syl.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege60c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume frege59c.a: |- A e. B


  assert |- ( A. x ( ph -> ( ps -> ch ) ) -> ( [. A / x ]. ps -> ( [. A / x ]. ph -> [. A / x ]. ch ) ) )

  proof
    wph
    wps
    wch
    wi
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    #
    wch
    vx
    cA
    wsbc
    #
    wi
    #
    wi
    #
    wi
    @2
    @4
    @3
    @5
    wi
    wi
    wi
    @2
    @1
    vx
    cA
    wsbc
    #
    @7
    @1
    vx
    cA
    cB
    frege59c.a
    frege58c
    @8
    @3
    @0
    vx
    cA
    wsbc
    @6
    wph
    @0
    vx
    cA
    sbcim1
    wps
    wch
    vx
    cA
    sbcim1
    syl6
    syl
    @2
    @3
    @4
    @5
    frege12
    ax-mp
end
