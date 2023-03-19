include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "c0v.mm"
include "wne.mm"
include "wi.mm"
include "elspansn3.mm"
include "3exp.mm"
include "com23.mm"
include "imp.mm"
include "ad2ant2r.mm"
include "spansnid.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "spansneleq.mm"
include "eleqtrrd.mm"
include "3expia.mm"
include "syl5.mm"
include "exp4b.mm"
include "com24.mm"
include "exp4a.mm"
include "imp43.mm"
include "impbid.mm"

theorem elspansn4
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. SH /\ B e. ~H ) /\ ( C e. ( span ` { B } ) /\ C =/= 0h ) ) -> ( B e. A <-> C e. A ) )

  proof
    cA
    csh
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    cC
    cB
    csn
    cspn
    cfv
    #
    wcel
    #
    cC
    c0v
    wne
    #
    wa
    wa
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    @0
    @3
    @5
    @6
    wi
    #
    @1
    @4
    @0
    @3
    @7
    @0
    @5
    @3
    @6
    @0
    @5
    @3
    @6
    cA
    cB
    cC
    elspansn3
    3exp
    com23
    imp
    ad2ant2r
    @0
    @1
    @3
    @4
    @6
    @5
    wi
    #
    @0
    @3
    @1
    @4
    @8
    wi
    @0
    @3
    @1
    @4
    @8
    @0
    @6
    @1
    @4
    wa
    #
    @3
    @5
    @0
    @6
    @9
    @3
    @5
    @9
    @3
    wa
    #
    cB
    cC
    csn
    cspn
    cfv
    #
    wcel
    #
    @0
    @6
    wa
    @5
    @10
    cB
    @2
    @11
    @1
    cB
    @2
    wcel
    @4
    @3
    cB
    spansnid
    ad2antrr
    @9
    @3
    @11
    @2
    wceq
    cC
    cB
    spansneleq
    imp
    eleqtrrd
    @0
    @6
    @12
    @5
    cA
    cC
    cB
    elspansn3
    3expia
    syl5
    exp4b
    com24
    exp4a
    com23
    imp43
    impbid
end
