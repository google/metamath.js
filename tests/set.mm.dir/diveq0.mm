include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "wa.mm"
include "wb.mm"
include "simp1.mm"
include "0cnd.mm"
include "3simpc.mm"
include "divmul2.mm"
include "syl3anc.mm"
include "simp2.mm"
include "mul01d.mm"
include "eqeq2d.mm"
include "bitrd.mm"

theorem diveq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( ( A / B ) = 0 <-> A = 0 ) )

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
    cc0
    wceq
    #
    cA
    cB
    cc0
    cmul
    co
    #
    wceq
    #
    cA
    cc0
    wceq
    @3
    @0
    cc0
    cc
    wcel
    @1
    @2
    wa
    @4
    @6
    wb
    @0
    @1
    @2
    simp1
    @3
    0cnd
    @0
    @1
    @2
    3simpc
    cA
    cc0
    cB
    divmul2
    syl3anc
    @3
    @5
    cc0
    cA
    @3
    cB
    @0
    @1
    @2
    simp2
    mul01d
    eqeq2d
    bitrd
end
