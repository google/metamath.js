include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "recid2.mm"
include "wb.mm"
include "1cnd.mm"
include "simpl.mm"
include "reccl.mm"
include "recne0.mm"
include "divmul.mm"
include "syl112anc.mm"
include "mpbird.mm"

theorem recrec
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( 1 / ( 1 / A ) ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    c1
    c1
    cA
    cdiv
    co
    #
    cdiv
    co
    cA
    wceq
    #
    @3
    cA
    cmul
    co
    c1
    wceq
    #
    cA
    recid2
    @2
    c1
    cc
    wcel
    @0
    @3
    cc
    wcel
    @3
    cc0
    wne
    @4
    @5
    wb
    @2
    1cnd
    @0
    @1
    simpl
    cA
    reccl
    cA
    recne0
    c1
    cA
    @3
    divmul
    syl112anc
    mpbird
end
