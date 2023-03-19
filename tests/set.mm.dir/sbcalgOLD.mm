include "wal.mm"
include "wsb.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "albidv.mm"
include "sbal.mm"
include "vtoclbg.mm"

theorem sbcalgOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  assert |- ( A e. V -> ( [. A / y ]. A. x ph <-> A. x [. A / y ]. ph ) )

  proof
    wph
    vx
    wal
    #
    vy
    vz
    wsb
    wph
    vy
    vz
    wsb
    #
    vx
    wal
    @0
    vy
    cA
    wsbc
    wph
    vy
    cA
    wsbc
    #
    vx
    wal
    vz
    cA
    cV
    @0
    vy
    vz
    cA
    dfsbcq2
    vz
    cv
    cA
    wceq
    @1
    @2
    vx
    wph
    vy
    vz
    cA
    dfsbcq2
    albidv
    wph
    vx
    vy
    vz
    sbal
    vtoclbg
end
