include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wceq.mm"
include "btwncom.mm"
include "wb.mm"
include "3anrev.mm"
include "sylan2b.mm"
include "anbi12d.mm"
include "wi.mm"
include "3ancomb.mm"
include "btwnswapid.mm"
include "sylbid.mm"

theorem btwnswapid2
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( ( A Btwn <. B , C >. /\ C Btwn <. B , A >. ) -> A = C ) )

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
    cbtwn
    wbr
    #
    cC
    cB
    cA
    cop
    cbtwn
    wbr
    #
    wa
    cA
    cC
    cB
    cop
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
    wa
    #
    cA
    cC
    wceq
    #
    @6
    @7
    @9
    @8
    @10
    cA
    cB
    cC
    cN
    btwncom
    @5
    @0
    @4
    @3
    @2
    w3a
    @8
    @10
    wb
    @2
    @3
    @4
    3anrev
    cC
    cB
    cA
    cN
    btwncom
    sylan2b
    anbi12d
    @5
    @0
    @2
    @4
    @3
    w3a
    @11
    @12
    wi
    @2
    @3
    @4
    3ancomb
    cA
    cC
    cB
    cN
    btwnswapid
    sylan2b
    sylbid
end
