include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cioo.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "elioo1.mm"
include "3adant3.mm"
include "3anass.mm"
include "baibr.mm"
include "3ad2ant3.mm"
include "bitr4d.mm"

theorem elioo5
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( C e. ( A (,) B ) <-> ( A < C /\ C < B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    cC
    cA
    cB
    cioo
    co
    wcel
    #
    @2
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    clt
    wbr
    #
    w3a
    #
    @4
    @5
    wa
    #
    @0
    @1
    @3
    @6
    wb
    @2
    cA
    cB
    cC
    elioo1
    3adant3
    @2
    @0
    @7
    @6
    wb
    @1
    @6
    @2
    @7
    @2
    @4
    @5
    3anass
    baibr
    3ad2ant3
    bitr4d
end
