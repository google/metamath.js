include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cec.mm"
include "cpnf.mm"
include "cbl.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "cr.mm"
include "w3a.mm"
include "xmeterval.mm"
include "3anass.mm"
include "baib.mm"
include "sylan9bb.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "a1i.mm"
include "elecg.mm"
include "sylan.mm"
include "xblpnf.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem xmetec
  let cD: class D
  let cP: class P
  let c.sm: class .~
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xmeter.1: |- .~ = ( `' D " RR )


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X ) -> [ P ] .~ = ( P ( ball ` D ) +oo ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    vx
    cP
    c.sm
    cec
    #
    cP
    cpnf
    cD
    cbl
    cfv
    co
    #
    @2
    cP
    vx
    cv
    #
    c.sm
    wbr
    #
    @5
    cX
    wcel
    #
    cP
    @5
    cD
    co
    cr
    wcel
    #
    wa
    #
    @5
    @3
    wcel
    #
    @5
    @4
    wcel
    @0
    @6
    @1
    @7
    @8
    w3a
    #
    @1
    @9
    cP
    @5
    cD
    c.sm
    cX
    xmeter.1
    xmeterval
    @11
    @1
    @9
    @1
    @7
    @8
    3anass
    baib
    sylan9bb
    @0
    @5
    cvv
    wcel
    #
    @1
    @10
    @6
    wb
    @12
    @0
    vx
    vex
    a1i
    @5
    cP
    c.sm
    cvv
    cX
    elecg
    sylan
    @5
    cD
    cP
    cX
    xblpnf
    3bitr4d
    eqrdv
end
