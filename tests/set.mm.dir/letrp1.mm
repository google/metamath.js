include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "ltp1.mm"
include "adantl.mm"
include "wi.mm"
include "peano2re.mm"
include "ancli.mm"
include "lelttr.mm"
include "3expb.mm"
include "sylan2.mm"
include "mpan2d.mm"
include "3impia.mm"
include "ltle.mm"
include "3adant3.mm"
include "mpd.mm"

theorem letrp1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> A <_ ( B + 1 ) )

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
    cB
    cle
    wbr
    #
    w3a
    cA
    cB
    c1
    caddc
    co
    #
    clt
    wbr
    #
    cA
    @3
    cle
    wbr
    #
    @0
    @1
    @2
    @4
    @0
    @1
    wa
    @2
    cB
    @3
    clt
    wbr
    #
    @4
    @1
    @6
    @0
    cB
    ltp1
    adantl
    @1
    @0
    @1
    @3
    cr
    wcel
    #
    wa
    @2
    @6
    wa
    @4
    wi
    #
    @1
    @7
    cB
    peano2re
    #
    ancli
    @0
    @1
    @7
    @8
    cA
    cB
    @3
    lelttr
    3expb
    sylan2
    mpan2d
    3impia
    @0
    @1
    @4
    @5
    wi
    #
    @2
    @1
    @0
    @7
    @10
    @9
    cA
    @3
    ltle
    sylan2
    3adant3
    mpd
end
