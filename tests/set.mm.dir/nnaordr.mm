include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "coa.mm"
include "co.mm"
include "nnaord.mm"
include "wceq.mm"
include "nnacom.mm"
include "ancoms.mm"
include "3adant2.mm"
include "3adant1.mm"
include "eleq12d.mm"
include "bitrd.mm"

theorem nnaordr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( A e. B <-> ( A +o C ) e. ( B +o C ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
    wcel
    #
    w3a
    #
    cA
    cB
    wcel
    cC
    cA
    coa
    co
    #
    cC
    cB
    coa
    co
    #
    wcel
    cA
    cC
    coa
    co
    #
    cB
    cC
    coa
    co
    #
    wcel
    cA
    cB
    cC
    nnaord
    @3
    @4
    @6
    @5
    @7
    @0
    @2
    @4
    @6
    wceq
    #
    @1
    @2
    @0
    @8
    cC
    cA
    nnacom
    ancoms
    3adant2
    @1
    @2
    @5
    @7
    wceq
    #
    @0
    @2
    @1
    @9
    cC
    cB
    nnacom
    ancoms
    3adant1
    eleq12d
    bitrd
end
