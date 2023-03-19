include "cvv.mm"
include "wcel.mm"
include "bj-csngl.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "isset.mm"
include "cpw.mm"
include "wss.mm"
include "pweq.mm"
include "eximi.mm"
include "bj-snglss.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "vpwex.mm"
include "ssex.mm"
include "exlimiv.mm"
include "3syl.mm"
include "sylbi.mm"
include "csn.mm"
include "cab.mm"
include "bj-snglinv.mm"
include "bj-snsetex.mm"
include "syl5eqel.mm"
include "impbii.mm"

theorem bj-snglex
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. _V <-> sngl A e. _V )

  proof
    cA
    cvv
    wcel
    #
    cA
    bj-csngl
    #
    cvv
    wcel
    #
    @0
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    #
    @2
    vx
    cA
    isset
    @5
    @3
    cpw
    #
    cA
    cpw
    #
    wceq
    #
    vx
    wex
    @1
    @6
    wss
    #
    vx
    wex
    @2
    @4
    @8
    vx
    @3
    cA
    pweq
    eximi
    @8
    @9
    vx
    @8
    @9
    @1
    @7
    wss
    cA
    bj-snglss
    @6
    @7
    @1
    sseq2
    mpbiri
    eximi
    @9
    @2
    vx
    @1
    @6
    vx
    vpwex
    ssex
    exlimiv
    3syl
    sylbi
    @2
    cA
    vy
    cv
    csn
    @1
    wcel
    vy
    cab
    cvv
    vy
    cA
    bj-snglinv
    vy
    @1
    cvv
    bj-snsetex
    syl5eqel
    impbii
end
