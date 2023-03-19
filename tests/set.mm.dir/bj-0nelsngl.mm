include "c0.mm"
include "bj-csngl.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "vex.mm"
include "snnz.mm"
include "nesymi.mm"
include "nex.mm"
include "wrex.mm"
include "bj-elsngl.mm"
include "rexex.mm"
include "sylbi.mm"
include "mto.mm"
include "nelir.mm"

theorem bj-0nelsngl
  let cA: class A
  let vx: setvar x


  assert |- (/) e/ sngl A

  proof
    c0
    cA
    bj-csngl
    #
    c0
    @0
    wcel
    #
    c0
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    #
    @4
    vx
    @3
    c0
    @2
    vx
    vex
    snnz
    nesymi
    nex
    @1
    @4
    vx
    cA
    wrex
    @5
    vx
    c0
    cA
    bj-elsngl
    @4
    vx
    cA
    rexex
    sylbi
    mto
    nelir
end
