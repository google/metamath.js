include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "eqid.mm"
include "wa.mm"
include "wb.mm"
include "simp2.mm"
include "simp1.mm"
include "mulcld.mm"
include "3simpc.mm"
include "divmul.mm"
include "syl3anc.mm"
include "mpbiri.mm"

theorem divcan3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( ( B x. A ) / B ) = A )

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
    cB
    cA
    cmul
    co
    #
    cB
    cdiv
    co
    cA
    wceq
    #
    @4
    @4
    wceq
    #
    @4
    eqid
    @3
    @4
    cc
    wcel
    @0
    @1
    @2
    wa
    @5
    @6
    wb
    @3
    cB
    cA
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp1
    #
    mulcld
    @7
    @0
    @1
    @2
    3simpc
    @4
    cA
    cB
    divmul
    syl3anc
    mpbiri
end
