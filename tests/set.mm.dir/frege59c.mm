include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "wn.mm"
include "frege58c.mm"
include "sbcim1.mm"
include "syl.mm"
include "frege30.mm"
include "ax-mp.mm"

theorem frege59c
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume frege59c.a: |- A e. B


  assert |- ( [. A / x ]. ph -> ( -. [. A / x ]. ps -> -. A. x ( ph -> ps ) ) )

  proof
    wph
    wps
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
    wi
    #
    wi
    @2
    @3
    wn
    @1
    wn
    wi
    wi
    @1
    @0
    vx
    cA
    wsbc
    @4
    @0
    vx
    cA
    cB
    frege59c.a
    frege58c
    wph
    wps
    vx
    cA
    sbcim1
    syl
    @1
    @2
    @3
    frege30
    ax-mp
end
