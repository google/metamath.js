include "ccmn.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cmnd.mm"
include "iscmn.mm"
include "simprbi.mm"
include "rsp2.mm"
include "imp.mm"
include "sylan.mm"
include "caovcomg.mm"
include "3impb.mm"

theorem cmncom
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cW: class W
  let cZ: class Z
  assume ablcom.b: |- B = ( Base ` G )
  assume ablcom.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. CMnd /\ X e. B /\ Y e. B ) -> ( X .+ Y ) = ( Y .+ X ) )

  proof
    cG
    ccmn
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.pl
    co
    cY
    cX
    c.pl
    co
    wceq
    @0
    vx
    vy
    cX
    cY
    cB
    c.pl
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    @2
    @1
    c.pl
    co
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @1
    cB
    wcel
    @2
    cB
    wcel
    wa
    #
    @3
    @0
    cG
    cmnd
    wcel
    @4
    vx
    vy
    cB
    c.pl
    cG
    ablcom.b
    ablcom.p
    iscmn
    simprbi
    @4
    @5
    @3
    @3
    vx
    vy
    cB
    cB
    rsp2
    imp
    sylan
    caovcomg
    3impb
end
