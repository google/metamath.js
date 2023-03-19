include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "chub1.mm"
include "ssid.mm"
include "jctil.mm"
include "ssin.mm"
include "sylib.mm"
include "inss1.mm"
include "eqss.mm"
include "sylibr.mm"

theorem chabs2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A i^i ( A vH B ) ) = A )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    wa
    #
    cA
    cA
    cB
    chj
    co
    #
    cin
    #
    cA
    wss
    #
    cA
    @2
    wss
    #
    wa
    @2
    cA
    wceq
    @0
    @4
    @3
    @0
    cA
    cA
    wss
    #
    cA
    @1
    wss
    #
    wa
    @4
    @0
    @6
    @5
    cA
    cB
    chub1
    cA
    ssid
    jctil
    cA
    cA
    @1
    ssin
    sylib
    cA
    @1
    inss1
    jctil
    @2
    cA
    eqss
    sylibr
end
