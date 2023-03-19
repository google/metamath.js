include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "cale.mm"
include "cfv.mm"
include "wss.mm"
include "wb.mm"
include "alephord2.mm"
include "ancoms.mm"
include "notbid.mm"
include "ontri1.mm"
include "alephon.mm"
include "mp2an.mm"
include "a1i.mm"
include "3bitr4d.mm"

theorem alephord3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> ( aleph ` A ) C_ ( aleph ` B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cB
    cA
    wcel
    #
    wn
    cB
    cale
    cfv
    #
    cA
    cale
    cfv
    #
    wcel
    #
    wn
    #
    cA
    cB
    wss
    @5
    @4
    wss
    #
    @2
    @3
    @6
    @1
    @0
    @3
    @6
    wb
    cB
    cA
    alephord2
    ancoms
    notbid
    cA
    cB
    ontri1
    @8
    @7
    wb
    #
    @2
    @5
    con0
    wcel
    @4
    con0
    wcel
    @9
    cA
    alephon
    cB
    alephon
    @5
    @4
    ontri1
    mp2an
    a1i
    3bitr4d
end
