include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cmul.mm"
include "wb.mm"
include "wa.mm"
include "ax-1cn.mm"
include "divmul2.mm"
include "mp3an2.mm"
include "3impb.mm"
include "simp2.mm"
include "mulid1d.mm"
include "eqeq2d.mm"
include "bitrd.mm"

theorem diveq1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( ( A / B ) = 1 <-> A = B ) )

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
    c1
    wceq
    #
    cA
    cB
    c1
    cmul
    co
    #
    wceq
    #
    cA
    cB
    wceq
    @0
    @1
    @2
    @4
    @6
    wb
    #
    @0
    c1
    cc
    wcel
    @1
    @2
    wa
    @7
    ax-1cn
    cA
    c1
    cB
    divmul2
    mp3an2
    3impb
    @3
    @5
    cB
    cA
    @3
    cB
    @0
    @1
    @2
    simp2
    mulid1d
    eqeq2d
    bitrd
end
