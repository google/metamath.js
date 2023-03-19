include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "ssid.mm"
include "inss1.mm"
include "pm3.2i.mm"
include "wb.mm"
include "simpl.mm"
include "chincl.mm"
include "chlub.mm"
include "syl3anc.mm"
include "mpbii.mm"
include "chub1.mm"
include "syldan.mm"
include "eqssd.mm"

theorem chabs1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A vH ( A i^i B ) ) = A )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cA
    cB
    cin
    #
    chj
    co
    #
    cA
    @2
    cA
    cA
    wss
    #
    @3
    cA
    wss
    #
    wa
    #
    @4
    cA
    wss
    #
    @5
    @6
    cA
    ssid
    cA
    cB
    inss1
    pm3.2i
    @2
    @0
    @3
    cch
    wcel
    #
    @0
    @7
    @8
    wb
    @0
    @1
    simpl
    #
    cA
    cB
    chincl
    #
    @10
    cA
    @3
    cA
    chlub
    syl3anc
    mpbii
    @0
    @1
    @9
    cA
    @4
    wss
    @11
    cA
    @3
    chub1
    syldan
    eqssd
end
