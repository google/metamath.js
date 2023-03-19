include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "weu.mm"
include "wex.mm"
include "nfeu1.mm"
include "nfcvd.mm"
include "eusvnf.mm"
include "nfeqd.mm"
include "nfrd.mm"
include "19.2.mm"
include "impbid1.mm"
include "eubid.mm"
include "ibir.mm"

theorem eusv2i
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A y
  assert |- ( E! y A. x y = A -> E! y E. x y = A )

  proof
    vy
    cv
    #
    cA
    wceq
    #
    vx
    wal
    #
    vy
    weu
    #
    @1
    vx
    wex
    #
    vy
    weu
    @3
    @4
    @2
    vy
    @2
    vy
    nfeu1
    @3
    @4
    @2
    @3
    @1
    vx
    @3
    vx
    @0
    cA
    @3
    vx
    @0
    nfcvd
    vx
    vy
    cA
    eusvnf
    nfeqd
    nfrd
    @1
    vx
    19.2
    impbid1
    eubid
    ibir
end
