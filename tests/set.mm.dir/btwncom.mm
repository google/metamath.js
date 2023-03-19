include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "btwncomim.mm"
include "wi.mm"
include "3ancomb.mm"
include "sylan2b.mm"
include "impbid.mm"

theorem btwncom
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( A Btwn <. B , C >. <-> A Btwn <. C , B >. ) )

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
    cA
    cB
    cC
    cop
    cbtwn
    wbr
    #
    cA
    cC
    cB
    cop
    cbtwn
    wbr
    #
    cA
    cB
    cC
    cN
    btwncomim
    @5
    @0
    @2
    @4
    @3
    w3a
    @7
    @6
    wi
    @2
    @3
    @4
    3ancomb
    cA
    cC
    cB
    cN
    btwncomim
    sylan2b
    impbid
end
