include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "intprg.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "prssi.mm"
include "prnzg.mm"
include "adantr.mm"
include "subrgint.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem subrgin
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( A e. ( SubRing ` R ) /\ B e. ( SubRing ` R ) ) -> ( A i^i B ) e. ( SubRing ` R ) )

  proof
    cA
    cR
    csubrg
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
    @0
    wss
    @4
    c0
    wne
    #
    @5
    @0
    wcel
    cA
    cB
    @0
    prssi
    @1
    @6
    @2
    cA
    cB
    @0
    prnzg
    adantr
    cR
    @4
    subrgint
    syl2anc
    eqeltrrd
end
