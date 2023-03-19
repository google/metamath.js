include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "eqid.mm"
include "preq2.mm"
include "eqeq2d.mm"
include "spcegv.mm"
include "mpi.mm"
include "a1d.mm"
include "wn.mm"
include "csn.mm"
include "dfsn2.mm"
include "prprc2.mm"
include "eqeq1d.mm"
include "exbidv.mm"
include "syl5ibr.mm"
include "pm2.61i.mm"

theorem elpreqprlem
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cV: class V
  let cA: class A

  disjoint B x
  disjoint C x
  disjoint A x
  assert |- ( B e. V -> E. x { B , C } = { B , x } )

  proof
    cC
    cvv
    wcel
    #
    cB
    cV
    wcel
    #
    cB
    cC
    cpr
    #
    cB
    vx
    cv
    #
    cpr
    #
    wceq
    #
    vx
    wex
    #
    wi
    @0
    @6
    @1
    @0
    @2
    @2
    wceq
    #
    @6
    @2
    eqid
    @5
    @7
    vx
    cC
    cvv
    @3
    cC
    wceq
    @4
    @2
    @2
    @3
    cC
    cB
    preq2
    eqeq2d
    spcegv
    mpi
    a1d
    @1
    @6
    @0
    wn
    #
    cB
    csn
    #
    @4
    wceq
    #
    vx
    wex
    #
    @1
    @9
    cB
    cB
    cpr
    #
    wceq
    #
    @11
    cB
    dfsn2
    @10
    @13
    vx
    cB
    cV
    @3
    cB
    wceq
    @4
    @12
    @9
    @3
    cB
    cB
    preq2
    eqeq2d
    spcegv
    mpi
    @8
    @5
    @10
    vx
    @8
    @2
    @9
    @4
    cB
    cC
    prprc2
    eqeq1d
    exbidv
    syl5ibr
    pm2.61i
end
