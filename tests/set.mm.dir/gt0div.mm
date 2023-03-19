include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "0re.mm"
include "ltdiv1.mm"
include "mp3an1.mm"
include "3impb.mm"
include "wne.mm"
include "wceq.mm"
include "gt0ne0.mm"
include "cc.mm"
include "recn.mm"
include "div0.mm"
include "sylan.mm"
include "syldan.mm"
include "breq1d.mm"
include "3adant1.mm"
include "bitrd.mm"

theorem gt0div
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ 0 < B ) -> ( 0 < A <-> 0 < ( A / B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    w3a
    cc0
    cA
    clt
    wbr
    #
    cc0
    cB
    cdiv
    co
    #
    cA
    cB
    cdiv
    co
    #
    clt
    wbr
    #
    cc0
    @5
    clt
    wbr
    #
    @0
    @1
    @2
    @3
    @6
    wb
    #
    cc0
    cr
    wcel
    @0
    @1
    @2
    wa
    #
    @8
    0re
    cc0
    cA
    cB
    ltdiv1
    mp3an1
    3impb
    @1
    @2
    @6
    @7
    wb
    @0
    @9
    @4
    cc0
    @5
    clt
    @1
    @2
    cB
    cc0
    wne
    #
    @4
    cc0
    wceq
    #
    cB
    gt0ne0
    @1
    cB
    cc
    wcel
    @10
    @11
    cB
    recn
    cB
    div0
    sylan
    syldan
    breq1d
    3adant1
    bitrd
end
