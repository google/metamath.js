include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "dfopg.mm"
include "snwf.mm"
include "adantr.mm"
include "prwf.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem opwf
  let cA: class A
  let cB: class B


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) -> <. A , B >. e. U. ( R1 " On ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
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
    cop
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    @0
    cA
    cB
    @0
    @0
    dfopg
    @3
    @4
    @0
    wcel
    #
    @5
    @0
    wcel
    @6
    @0
    wcel
    @1
    @7
    @2
    cA
    snwf
    adantr
    cA
    cB
    prwf
    @4
    @5
    prwf
    syl2anc
    eqeltrd
end
