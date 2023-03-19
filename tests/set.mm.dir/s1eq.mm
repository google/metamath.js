include "wceq.mm"
include "cc0.mm"
include "cid.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cs1.mm"
include "fveq2.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "df-s1.mm"
include "3eqtr4g.mm"

theorem s1eq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> <" A "> = <" B "> )

  proof
    cA
    cB
    wceq
    #
    cc0
    cA
    cid
    cfv
    #
    cop
    #
    csn
    cc0
    cB
    cid
    cfv
    #
    cop
    #
    csn
    cA
    cs1
    cB
    cs1
    @0
    @2
    @4
    @0
    @1
    @3
    cc0
    cA
    cB
    cid
    fveq2
    opeq2d
    sneqd
    cA
    df-s1
    cB
    df-s1
    3eqtr4g
end
