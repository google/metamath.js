include "cv.mm"
include "wceq.mm"
include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "isset.mm"
include "eueq.mm"
include "sylbb1.mm"
include "df-mo.mm"
include "mpbir.mm"

theorem moeq
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- E* x x = A

  proof
    vx
    cv
    cA
    wceq
    #
    vx
    wmo
    @0
    vx
    wex
    #
    @0
    vx
    weu
    #
    wi
    cA
    cvv
    wcel
    @1
    @2
    vx
    cA
    isset
    vx
    cA
    eueq
    sylbb1
    @0
    vx
    df-mo
    mpbir
end
