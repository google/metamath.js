include "con0.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wwe.mm"
include "wex.mm"
include "ccrd.mm"
include "cdm.mm"
include "wrex.mm"
include "breq2.mm"
include "rspcev.mm"
include "ac10ct.mm"
include "syl.mm"
include "ween.mm"
include "sylibr.mm"

theorem ondomen
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vr: setvar r


  assert |- ( ( A e. On /\ B ~<_ A ) -> B e. dom card )

  proof
    cA
    con0
    wcel
    cB
    cA
    cdom
    wbr
    #
    wa
    #
    cB
    vr
    cv
    wwe
    vr
    wex
    #
    cB
    ccrd
    cdm
    wcel
    @1
    cB
    vx
    cv
    #
    cdom
    wbr
    #
    vx
    con0
    wrex
    @2
    @4
    @0
    vx
    cA
    con0
    @3
    cA
    cB
    cdom
    breq2
    rspcev
    vr
    vx
    cB
    ac10ct
    syl
    cB
    vr
    ween
    sylibr
end
