include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "cxp.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "xpeq1.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "vex.mm"
include "xpdom2.mm"
include "vtoclg.mm"
include "imp.mm"

theorem xpdom2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vx: setvar x
  let cW: class W


  assert |- ( ( C e. V /\ A ~<_ B ) -> ( C X. A ) ~<_ ( C X. B ) )

  proof
    cC
    cV
    wcel
    cA
    cB
    cdom
    wbr
    #
    cC
    cA
    cxp
    #
    cC
    cB
    cxp
    #
    cdom
    wbr
    #
    @0
    vx
    cv
    #
    cA
    cxp
    #
    @4
    cB
    cxp
    #
    cdom
    wbr
    #
    wi
    @0
    @3
    wi
    vx
    cC
    cV
    @4
    cC
    wceq
    #
    @7
    @3
    @0
    @8
    @5
    @1
    @6
    @2
    cdom
    @4
    cC
    cA
    xpeq1
    @4
    cC
    cB
    xpeq1
    breq12d
    imbi2d
    cA
    cB
    @4
    vx
    vex
    xpdom2
    vtoclg
    imp
end
