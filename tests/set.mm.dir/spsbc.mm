include "wal.mm"
include "wsbc.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "wsb.mm"
include "stdpc4.mm"
include "sbsbc.mm"
include "sylib.mm"
include "dfsbcq.mm"
include "syl5ib.mm"
include "vtocleg.mm"

theorem spsbc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> ( A. x ph -> [. A / x ]. ph ) )

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
    vy
    cA
    cV
    @0
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    @2
    cA
    wceq
    @1
    @0
    wph
    vx
    vy
    wsb
    @3
    wph
    vx
    vy
    stdpc4
    wph
    vx
    vy
    sbsbc
    sylib
    wph
    vx
    @2
    cA
    dfsbcq
    syl5ib
    vtocleg
end
