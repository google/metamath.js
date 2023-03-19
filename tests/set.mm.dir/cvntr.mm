include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "ccv.mm"
include "wbr.mm"
include "wpss.mm"
include "wn.mm"
include "wi.mm"
include "cvpss.mm"
include "3adant3.mm"
include "3adant1.mm"
include "wa.mm"
include "cvnbtwn.mm"
include "3com23.mm"
include "con2d.mm"
include "syl2and.mm"

theorem cvntr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( ( A <oH B /\ B <oH C ) -> -. A <oH C ) )

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
    ccv
    wbr
    #
    cA
    cB
    wpss
    #
    cB
    cC
    ccv
    wbr
    #
    cB
    cC
    wpss
    #
    cA
    cC
    ccv
    wbr
    #
    wn
    @0
    @1
    @4
    @5
    wi
    @2
    cA
    cB
    cvpss
    3adant3
    @1
    @2
    @6
    @7
    wi
    @0
    cB
    cC
    cvpss
    3adant1
    @3
    @8
    @5
    @7
    wa
    #
    @0
    @2
    @1
    @8
    @9
    wn
    wi
    cA
    cC
    cB
    cvnbtwn
    3com23
    con2d
    syl2and
end
