include "con0.mm"
include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "coa.mm"
include "co.mm"
include "wss.mm"
include "wb.mm"
include "oaord.mm"
include "3com12.mm"
include "notbid.mm"
include "ontri1.mm"
include "3adant3.mm"
include "oacl.mm"
include "ancoms.mm"
include "3adant2.mm"
include "3adant1.mm"
include "syl2anc.mm"
include "3bitr4d.mm"

theorem oaword
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( A C_ B <-> ( C +o A ) C_ ( C +o B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    w3a
    #
    cB
    cA
    wcel
    #
    wn
    #
    cC
    cB
    coa
    co
    #
    cC
    cA
    coa
    co
    #
    wcel
    #
    wn
    #
    cA
    cB
    wss
    #
    @7
    @6
    wss
    #
    @3
    @4
    @8
    @1
    @0
    @2
    @4
    @8
    wb
    cB
    cA
    cC
    oaord
    3com12
    notbid
    @0
    @1
    @10
    @5
    wb
    @2
    cA
    cB
    ontri1
    3adant3
    @3
    @7
    con0
    wcel
    #
    @6
    con0
    wcel
    #
    @11
    @9
    wb
    @0
    @2
    @12
    @1
    @2
    @0
    @12
    cC
    cA
    oacl
    ancoms
    3adant2
    @1
    @2
    @13
    @0
    @2
    @1
    @13
    cC
    cB
    oacl
    ancoms
    3adant1
    @7
    @6
    ontri1
    syl2anc
    3bitr4d
end
