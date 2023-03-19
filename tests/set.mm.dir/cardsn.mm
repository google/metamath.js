include "wcel.mm"
include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "ccrd.mm"
include "cfv.mm"
include "c1o.mm"
include "eqid.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "spcegv.mm"
include "mpi.mm"
include "card1.mm"
include "sylibr.mm"

theorem cardsn
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( card ` { A } ) = 1o )

  proof
    cA
    cV
    wcel
    #
    cA
    csn
    #
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
    @1
    ccrd
    cfv
    c1o
    wceq
    @0
    @1
    @1
    wceq
    #
    @5
    @1
    eqid
    @4
    @6
    vx
    cA
    cV
    @2
    cA
    wceq
    @3
    @1
    @1
    @2
    cA
    sneq
    eqeq2d
    spcegv
    mpi
    vx
    @1
    card1
    sylibr
end
