include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wb.mm"
include "simp1.mm"
include "simp3l.mm"
include "remulcld.mm"
include "ltdiv1.mm"
include "syld3an1.mm"
include "recnd.mm"
include "simp3r.mm"
include "gt0ne0d.mm"
include "divcan4d.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem ltmuldiv
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( ( A x. C ) < B <-> A < ( B / C ) ) )

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
    #
    w3a
    #
    cA
    cC
    cmul
    co
    #
    cB
    clt
    wbr
    #
    @6
    cC
    cdiv
    co
    #
    cB
    cC
    cdiv
    co
    #
    clt
    wbr
    #
    cA
    @9
    clt
    wbr
    @6
    cr
    wcel
    @1
    @0
    @4
    @7
    @10
    wb
    @5
    cA
    cC
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @2
    @3
    simp3l
    #
    remulcld
    @6
    cB
    cC
    ltdiv1
    syld3an1
    @5
    @8
    cA
    @9
    clt
    @5
    cA
    cC
    @5
    cA
    @11
    recnd
    @5
    cC
    @12
    recnd
    @5
    cC
    @0
    @1
    @2
    @3
    simp3r
    gt0ne0d
    divcan4d
    breq1d
    bitrd
end
