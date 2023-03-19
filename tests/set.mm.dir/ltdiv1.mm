include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "gt0ne0d.mm"
include "rereccld.mm"
include "recgt0.mm"
include "3ad2ant3.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "recnd.mm"
include "divrecd.mm"
include "breq12d.mm"
include "bitr4d.mm"

theorem ltdiv1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( A < B <-> ( A / C ) < ( B / C ) ) )

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
    cB
    clt
    wbr
    #
    cA
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    cB
    @7
    cmul
    co
    #
    clt
    wbr
    #
    cA
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
    @5
    @0
    @1
    @7
    cr
    wcel
    cc0
    @7
    clt
    wbr
    #
    @6
    @10
    wb
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @4
    simp2
    #
    @5
    cC
    @0
    @1
    @2
    @3
    simp3l
    #
    @5
    cC
    @0
    @1
    @2
    @3
    simp3r
    gt0ne0d
    #
    rereccld
    @4
    @0
    @13
    @1
    cC
    recgt0
    3ad2ant3
    cA
    cB
    @7
    ltmul1
    syl112anc
    @5
    @11
    @8
    @12
    @9
    clt
    @5
    cA
    cC
    @5
    cA
    @14
    recnd
    @5
    cC
    @16
    recnd
    #
    @17
    divrecd
    @5
    cB
    cC
    @5
    cB
    @15
    recnd
    @18
    @17
    divrecd
    breq12d
    bitr4d
end
