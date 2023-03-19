include "con0.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "ccrd.mm"
include "cdm.mm"
include "breq1.mm"
include "rspcev.mm"
include "isnum2.mm"
include "sylibr.mm"

theorem isnumi
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. On /\ A ~~ B ) -> B e. dom card )

  proof
    cA
    con0
    wcel
    cA
    cB
    cen
    wbr
    #
    wa
    vx
    cv
    #
    cB
    cen
    wbr
    #
    vx
    con0
    wrex
    cB
    ccrd
    cdm
    wcel
    @2
    @0
    vx
    cA
    con0
    @1
    cA
    cB
    cen
    breq1
    rspcev
    vx
    cB
    isnum2
    sylibr
end
