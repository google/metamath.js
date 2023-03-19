include "word.mm"
include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cun.mm"
include "wss.mm"
include "prssi.mm"
include "3adant1.mm"
include "con0.mm"
include "ordelon.mm"
include "3adant3.mm"
include "3adant2.mm"
include "ordunpr.mm"
include "syl2anc.mm"
include "sseldd.mm"

theorem ordunel
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Ord A /\ B e. A /\ C e. A ) -> ( B u. C ) e. A )

  proof
    cA
    word
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    w3a
    #
    cB
    cC
    cpr
    #
    cA
    cB
    cC
    cun
    #
    @1
    @2
    @4
    cA
    wss
    @0
    cB
    cC
    cA
    prssi
    3adant1
    @3
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    @5
    @4
    wcel
    @0
    @1
    @6
    @2
    cA
    cB
    ordelon
    3adant3
    @0
    @2
    @7
    @1
    cA
    cC
    ordelon
    3adant2
    cB
    cC
    ordunpr
    syl2anc
    sseldd
end
