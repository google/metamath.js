include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "intprg.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "prnzg.mm"
include "adantr.mm"
include "prssi.mm"
include "intcld.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem incld
  let cA: class A
  let cB: class B
  let cJ: class J


  assert |- ( ( A e. ( Clsd ` J ) /\ B e. ( Clsd ` J ) ) -> ( A i^i B ) e. ( Clsd ` J ) )

  proof
    cA
    cJ
    ccld
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    cpr
    #
    cint
    #
    cA
    cB
    cin
    @0
    cA
    cB
    @0
    @0
    intprg
    @3
    @4
    c0
    wne
    #
    @4
    @0
    wss
    @5
    @0
    wcel
    @1
    @6
    @2
    cA
    cB
    @0
    prnzg
    adantr
    cA
    cB
    @0
    prssi
    @4
    cJ
    intcld
    syl2anc
    eqeltrrd
end
