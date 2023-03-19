include "cv.mm"
include "wcel.mm"
include "weu.mm"
include "cab.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "euabsn.mm"
include "abid2.mm"
include "eqeq1i.mm"
include "exbii.mm"
include "bitri.mm"

theorem eusn
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( E! x x e. A <-> E. x A = { x } )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vx
    weu
    @1
    vx
    cab
    #
    @0
    csn
    #
    wceq
    #
    vx
    wex
    cA
    @3
    wceq
    #
    vx
    wex
    @1
    vx
    euabsn
    @4
    @5
    vx
    @2
    cA
    @3
    vx
    cA
    abid2
    eqeq1i
    exbii
    bitri
end
