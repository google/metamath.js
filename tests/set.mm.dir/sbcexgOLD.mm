include "wex.mm"
include "wsb.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "exbidv.mm"
include "sbex.mm"
include "vtoclbg.mm"

theorem sbcexgOLD
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
  assert |- ( A e. V -> ( [. A / y ]. E. x ph <-> E. x [. A / y ]. ph ) )

  proof
    wph
    vx
    wex
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
    wex
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
    wex
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
    exbidv
    wph
    vx
    vy
    vz
    sbex
    vtoclbg
end
