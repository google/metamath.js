include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "ccv.mm"
include "wbr.mm"
include "wpss.mm"
include "wn.mm"
include "cvpss.mm"
include "wi.mm"
include "ancoms.mm"
include "pssn2lp.mm"
include "imnani.mm"
include "syl6.mm"
include "con2d.mm"
include "syld.mm"

theorem cvnsym
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A <oH B -> -. B <oH A ) )

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
    cB
    ccv
    wbr
    cA
    cB
    wpss
    #
    cB
    cA
    ccv
    wbr
    #
    wn
    cA
    cB
    cvpss
    @2
    @4
    @3
    @2
    @4
    cB
    cA
    wpss
    #
    @3
    wn
    @1
    @0
    @4
    @5
    wi
    cB
    cA
    cvpss
    ancoms
    @5
    @3
    cB
    cA
    pssn2lp
    imnani
    syl6
    con2d
    syld
end
