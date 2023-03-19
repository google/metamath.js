include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "cmd.mm"
include "wbr.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "mdi.mm"
include "3adantr2.mm"
include "wb.mm"
include "chincl.mm"
include "chlejb2.mm"
include "stoic3.mm"
include "biimpa.mm"
include "3ad2antr2.mm"
include "eqtrd.mm"

theorem mdsl3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ ( A MH B /\ ( A i^i B ) C_ C /\ C C_ B ) ) -> ( ( C vH A ) i^i B ) = C )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    w3a
    #
    cA
    cB
    cmd
    wbr
    #
    cA
    cB
    cin
    #
    cC
    wss
    #
    cC
    cB
    wss
    #
    w3a
    wa
    cC
    cA
    chj
    co
    cB
    cin
    #
    cC
    @5
    chj
    co
    #
    cC
    @3
    @4
    @7
    @8
    @9
    wceq
    @6
    cA
    cB
    cC
    mdi
    3adantr2
    @3
    @4
    @6
    @9
    cC
    wceq
    #
    @7
    @3
    @6
    @10
    @0
    @1
    @5
    cch
    wcel
    @2
    @6
    @10
    wb
    cA
    cB
    chincl
    @5
    cC
    chlejb2
    stoic3
    biimpa
    3ad2antr2
    eqtrd
end
