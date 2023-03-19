include "cop.mm"
include "csn.mm"
include "wfun.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "funsn.mm"
include "opex.mm"
include "snid.mm"
include "funopfv.mm"
include "mp2.mm"

theorem fvsn
  let cA: class A
  let cB: class B
  assume fvsn.1: |- A e. _V
  assume fvsn.2: |- B e. _V


  assert |- ( { <. A , B >. } ` A ) = B

  proof
    cA
    cB
    cop
    #
    csn
    #
    wfun
    @0
    @1
    wcel
    cA
    @1
    cfv
    cB
    wceq
    cA
    cB
    fvsn.1
    fvsn.2
    funsn
    @0
    cA
    cB
    opex
    snid
    cA
    cB
    @1
    funopfv
    mp2
end
