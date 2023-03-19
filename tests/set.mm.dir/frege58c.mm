include "wcel.mm"
include "wal.mm"
include "wsbc.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "wsb.mm"
include "ax-frege58b.mm"
include "sbsbc.mm"
include "sylib.mm"
include "dfsbcq.mm"
include "syl5ib.mm"
include "vtocleg.mm"
include "ax-mp.mm"

theorem frege58c
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume frege58c.a: |- A e. B


  assert |- ( A. x ph -> [. A / x ]. ph )

  proof
    cA
    cB
    wcel
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
    #
    frege58c.a
    @2
    vy
    cA
    cB
    @0
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    @3
    cA
    wceq
    @1
    @0
    wph
    vx
    vy
    wsb
    @4
    wph
    vx
    vy
    ax-frege58b
    wph
    vx
    vy
    sbsbc
    sylib
    wph
    vx
    @3
    cA
    dfsbcq
    syl5ib
    vtocleg
    ax-mp
end
