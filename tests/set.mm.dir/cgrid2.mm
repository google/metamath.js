include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "cgrcom.mm"
include "syl122anc.mm"
include "wi.mm"
include "3anrot.mm"
include "axcgrid.mm"
include "sylan2b.mm"
include "sylbid.mm"

theorem cgrid2
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( <. A , A >. Cgr <. B , C >. -> B = C ) )

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
    cA
    cop
    #
    cB
    cC
    cop
    #
    ccgr
    wbr
    #
    @8
    @7
    ccgr
    wbr
    #
    cB
    cC
    wceq
    #
    @6
    @0
    @2
    @2
    @3
    @4
    @9
    @10
    wb
    @0
    @5
    simpl
    @0
    @2
    @3
    @4
    simpr1
    #
    @12
    @0
    @2
    @3
    @4
    simpr2
    @0
    @2
    @3
    @4
    simpr3
    cA
    cA
    cB
    cC
    cN
    cgrcom
    syl122anc
    @5
    @0
    @3
    @4
    @2
    w3a
    @10
    @11
    wi
    @2
    @3
    @4
    3anrot
    cB
    cC
    cA
    cN
    axcgrid
    sylan2b
    sylbid
end
