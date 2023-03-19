include "cq.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "qcn.mm"
include "id.mm"
include "divrec.mm"
include "syl3an.mm"
include "wa.mm"
include "qreccl.mm"
include "qmulcl.mm"
include "sylan2.mm"
include "3impb.mm"
include "eqeltrd.mm"

theorem qdivcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. QQ /\ B e. QQ /\ B =/= 0 ) -> ( A / B ) e. QQ )

  proof
    cA
    cq
    wcel
    #
    cB
    cq
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    cA
    cB
    cdiv
    co
    #
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    cq
    @0
    cA
    cc
    wcel
    @1
    cB
    cc
    wcel
    @2
    @2
    @3
    @5
    wceq
    cA
    qcn
    cB
    qcn
    @2
    id
    cA
    cB
    divrec
    syl3an
    @0
    @1
    @2
    @5
    cq
    wcel
    #
    @1
    @2
    wa
    @0
    @4
    cq
    wcel
    @6
    cB
    qreccl
    cA
    @4
    qmulcl
    sylan2
    3impb
    eqeltrd
end
