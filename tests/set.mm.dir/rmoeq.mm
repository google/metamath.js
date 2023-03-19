include "cv.mm"
include "wceq.mm"
include "wrmo.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "moeq.mm"
include "moani.mm"
include "df-rmo.mm"
include "mpbir.mm"

theorem rmoeq
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- E* x e. B x = A

  proof
    vx
    cv
    #
    cA
    wceq
    #
    vx
    cB
    wrmo
    @0
    cB
    wcel
    #
    @1
    wa
    vx
    wmo
    @1
    @2
    vx
    vx
    cA
    moeq
    moani
    @1
    vx
    cB
    df-rmo
    mpbir
end
