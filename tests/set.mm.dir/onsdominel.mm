include "con0.mm"
include "wcel.mm"
include "cin.mm"
include "csdm.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "ontri1.mm"
include "ancoms.mm"
include "wi.mm"
include "cdom.mm"
include "cvv.mm"
include "inex1g.mm"
include "ssrin.mm"
include "ssdomg.mm"
include "syl2im.mm"
include "domnsym.mm"
include "syl6.mm"
include "adantr.mm"
include "sylbird.mm"
include "con4d.mm"
include "3impia.mm"

theorem onsdominel
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ ( A i^i C ) ~< ( B i^i C ) ) -> A e. B )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    cC
    cin
    #
    cB
    cC
    cin
    #
    csdm
    wbr
    #
    cA
    cB
    wcel
    #
    @0
    @1
    wa
    #
    @5
    @4
    @6
    @5
    wn
    #
    cB
    cA
    wss
    #
    @4
    wn
    #
    @1
    @0
    @8
    @7
    wb
    cB
    cA
    ontri1
    ancoms
    @0
    @8
    @9
    wi
    @1
    @0
    @8
    @3
    @2
    cdom
    wbr
    #
    @9
    @0
    @2
    cvv
    wcel
    @8
    @3
    @2
    wss
    @10
    cA
    cC
    con0
    inex1g
    cB
    cA
    cC
    ssrin
    @3
    @2
    cvv
    ssdomg
    syl2im
    @3
    @2
    domnsym
    syl6
    adantr
    sylbird
    con4d
    3impia
end
