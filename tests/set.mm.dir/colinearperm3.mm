include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "w3o.mm"
include "ccolin.mm"
include "wb.mm"
include "3orrot.mm"
include "a1i.mm"
include "brcolinear.mm"
include "3anrot.mm"
include "sylan2b.mm"
include "3bitr4d.mm"

theorem colinearperm3
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( A Colinear <. B , C >. <-> B Colinear <. C , A >. ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cop
    #
    cbtwn
    wbr
    #
    cB
    cC
    cA
    cop
    #
    cbtwn
    wbr
    #
    cC
    cA
    cB
    cop
    cbtwn
    wbr
    #
    w3o
    #
    @10
    @11
    @8
    w3o
    #
    cA
    @7
    ccolin
    wbr
    cB
    @9
    ccolin
    wbr
    #
    @12
    @13
    wb
    @6
    @8
    @10
    @11
    3orrot
    a1i
    cA
    cB
    cC
    cN
    brcolinear
    @5
    @0
    @3
    @4
    @2
    w3a
    @14
    @13
    wb
    @2
    @3
    @4
    3anrot
    cB
    cC
    cA
    cN
    brcolinear
    sylan2b
    3bitr4d
end
