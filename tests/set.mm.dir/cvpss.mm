include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "ccv.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "cvbr.mm"
include "simpl.mm"
include "syl6bi.mm"

theorem cvpss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A <oH B -> A C. B ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    wa
    cA
    cB
    ccv
    wbr
    cA
    cB
    wpss
    #
    cA
    vx
    cv
    #
    wpss
    @1
    cB
    wpss
    wa
    vx
    cch
    wrex
    wn
    #
    wa
    @0
    vx
    cA
    cB
    cvbr
    @0
    @2
    simpl
    syl6bi
end
