include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "ltmul1.mm"
include "wb.mm"
include "cc.mm"
include "recn.mm"
include "wceq.mm"
include "mulcom.mm"
include "sylan.mm"
include "3adant2.mm"
include "3adant1.mm"
include "breq12d.mm"
include "syl3an3.mm"
include "3adant3r.mm"
include "bitrd.mm"

theorem ltmul2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( A < B <-> ( C x. A ) < ( C x. B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    wa
    w3a
    cA
    cB
    clt
    wbr
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    clt
    wbr
    #
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    clt
    wbr
    #
    cA
    cB
    cC
    ltmul1
    @0
    @1
    @2
    @6
    @9
    wb
    #
    @3
    @2
    @0
    @1
    cC
    cc
    wcel
    #
    @10
    cC
    recn
    @0
    @1
    @11
    w3a
    @4
    @7
    @5
    @8
    clt
    @0
    @11
    @4
    @7
    wceq
    #
    @1
    @0
    cA
    cc
    wcel
    @11
    @12
    cA
    recn
    cA
    cC
    mulcom
    sylan
    3adant2
    @1
    @11
    @5
    @8
    wceq
    #
    @0
    @1
    cB
    cc
    wcel
    @11
    @13
    cB
    recn
    cB
    cC
    mulcom
    sylan
    3adant1
    breq12d
    syl3an3
    3adant3r
    bitrd
end
