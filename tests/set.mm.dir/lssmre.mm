include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "wi.mm"
include "wss.mm"
include "lssss.mm"
include "selpw.mm"
include "sylibr.mm"
include "a1i.mm"
include "ssrdv.mm"
include "lss1.mm"
include "lssintcl.mm"
include "ismred.mm"

theorem lssmre
  let cB: class B
  let cS: class S
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume lssacs.b: |- B = ( Base ` W )
  assume lssacs.s: |- S = ( LSubSp ` W )


  assert |- ( W e. LMod -> S e. ( Moore ` B ) )

  proof
    cW
    clmod
    wcel
    #
    cS
    cB
    va
    @0
    va
    cS
    cB
    cpw
    #
    va
    cv
    #
    cS
    wcel
    #
    @2
    @1
    wcel
    #
    wi
    @0
    @3
    @2
    cB
    wss
    @4
    cS
    @2
    cB
    cW
    lssacs.b
    lssacs.s
    lssss
    va
    cB
    selpw
    sylibr
    a1i
    ssrdv
    cS
    cB
    cW
    lssacs.b
    lssacs.s
    lss1
    @2
    cS
    cW
    lssacs.s
    lssintcl
    ismred
end
