include "clmod.mm"
include "wcel.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "scaffval.mm"
include "fmpt2.mm"
include "sylib.mm"

theorem lmodscaf
  let cB: class B
  let c.xb: class .xb
  let cF: class F
  let cK: class K
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume scaffval.b: |- B = ( Base ` W )
  assume scaffval.f: |- F = ( Scalar ` W )
  assume scaffval.k: |- K = ( Base ` F )
  assume scaffval.a: |- .xb = ( .sf ` W )


  assert |- ( W e. LMod -> .xb : ( K X. B ) --> B )

  proof
    cW
    clmod
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cK
    wral
    cK
    cB
    cxp
    cB
    c.xb
    wf
    @0
    @5
    vx
    vy
    cK
    cB
    @0
    @1
    cK
    wcel
    @2
    cB
    wcel
    @5
    @1
    @3
    cF
    cK
    cB
    cW
    @2
    scaffval.b
    scaffval.f
    @3
    eqid
    #
    scaffval.k
    lmodvscl
    3expb
    ralrimivva
    vx
    vy
    cK
    cB
    @4
    cB
    c.xb
    vx
    vy
    cB
    c.xb
    @3
    cF
    cK
    cW
    scaffval.b
    scaffval.f
    scaffval.k
    scaffval.a
    @6
    scaffval
    fmpt2
    sylib
end
