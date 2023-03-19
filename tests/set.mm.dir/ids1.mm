include "cc0.mm"
include "cid.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cs1.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "opeq2i.mm"
include "sneqi.mm"
include "df-s1.mm"
include "3eqtr4ri.mm"

theorem ids1
  let cA: class A


  assert |- <" A "> = <" ( _I ` A ) ">

  proof
    cc0
    cA
    cid
    cfv
    #
    cid
    cfv
    #
    cop
    #
    csn
    cc0
    @0
    cop
    #
    csn
    @0
    cs1
    cA
    cs1
    @2
    @3
    @1
    @0
    cc0
    @0
    cvv
    wcel
    @1
    @0
    wceq
    cA
    cid
    fvex
    @0
    cvv
    fvi
    ax-mp
    opeq2i
    sneqi
    @0
    df-s1
    cA
    df-s1
    3eqtr4ri
end
