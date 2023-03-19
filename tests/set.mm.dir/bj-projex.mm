include "wcel.mm"
include "bj-cproj.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cab.mm"
include "cvv.mm"
include "df-bj-proj.mm"
include "bj-clex.mm"
include "syl5eqel.mm"

theorem bj-projex
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( B e. V -> ( A Proj B ) e. _V )

  proof
    cB
    cV
    wcel
    cA
    cB
    bj-cproj
    vx
    cv
    csn
    cB
    cA
    csn
    #
    cima
    wcel
    vx
    cab
    cvv
    vx
    cA
    cB
    df-bj-proj
    vx
    cB
    @0
    cV
    bj-clex
    syl5eqel
end
