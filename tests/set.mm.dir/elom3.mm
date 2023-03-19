include "com.mm"
include "wcel.mm"
include "con0.mm"
include "cv.mm"
include "wlim.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "elom.mm"
include "limom.mm"
include "omex.mm"
include "wceq.mm"
include "limeq.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "spcv.mm"
include "mpi.mm"
include "nnon.mm"
include "syl.mm"
include "pm4.71ri.mm"
include "bitr4i.mm"

theorem elom3
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. _om <-> A. x ( Lim x -> A e. x ) )

  proof
    cA
    com
    wcel
    #
    cA
    con0
    wcel
    #
    vx
    cv
    #
    wlim
    #
    cA
    @2
    wcel
    #
    wi
    #
    vx
    wal
    #
    wa
    @6
    vx
    cA
    elom
    @6
    @1
    @6
    @0
    @1
    @6
    com
    wlim
    #
    @0
    limom
    @5
    @7
    @0
    wi
    vx
    com
    omex
    @2
    com
    wceq
    @3
    @7
    @4
    @0
    @2
    com
    limeq
    @2
    com
    cA
    eleq2
    imbi12d
    spcv
    mpi
    cA
    nnon
    syl
    pm4.71ri
    bitr4i
end
