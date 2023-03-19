include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "eqid.mm"
include "wa.mm"
include "wb.mm"
include "simp1.mm"
include "divcl.mm"
include "3simpc.mm"
include "divmul.mm"
include "syl3anc.mm"
include "mpbii.mm"

theorem divcan2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( B x. ( A / B ) ) = A )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    #
    @4
    wceq
    #
    cB
    @4
    cmul
    co
    cA
    wceq
    #
    @4
    eqid
    @3
    @0
    @4
    cc
    wcel
    @1
    @2
    wa
    @5
    @6
    wb
    @0
    @1
    @2
    simp1
    cA
    cB
    divcl
    @0
    @1
    @2
    3simpc
    cA
    @4
    cB
    divmul
    syl3anc
    mpbii
end
