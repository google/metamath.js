include "cq.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "qcn.mm"
include "negsub.mm"
include "syl2an.mm"
include "qnegcl.mm"
include "qaddcl.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem qsubcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. QQ /\ B e. QQ ) -> ( A - B ) e. QQ )

  proof
    cA
    cq
    wcel
    #
    cB
    cq
    wcel
    #
    wa
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cq
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @3
    @4
    wceq
    @1
    cA
    qcn
    cB
    qcn
    cA
    cB
    negsub
    syl2an
    @1
    @0
    @2
    cq
    wcel
    @3
    cq
    wcel
    cB
    qnegcl
    cA
    @2
    qaddcl
    sylan2
    eqeltrrd
end
