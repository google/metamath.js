include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "lep1.mm"
include "adantr.mm"
include "wi.mm"
include "peano2re.mm"
include "ancli.mm"
include "letr.mm"
include "3expa.mm"
include "sylan.mm"
include "mpand.mm"
include "3impia.mm"

theorem p1le
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ ( A + 1 ) <_ B ) -> A <_ B )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    c1
    caddc
    co
    #
    cB
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    @0
    @1
    wa
    cA
    @2
    cle
    wbr
    #
    @3
    @4
    @0
    @5
    @1
    cA
    lep1
    adantr
    @0
    @0
    @2
    cr
    wcel
    #
    wa
    @1
    @5
    @3
    wa
    @4
    wi
    #
    @0
    @6
    cA
    peano2re
    ancli
    @0
    @6
    @1
    @7
    cA
    @2
    cB
    letr
    3expa
    sylan
    mpand
    3impia
end
