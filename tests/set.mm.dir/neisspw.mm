include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "neii1.mm"
include "selpw.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"

theorem neisspw
  let cS: class S
  let cJ: class J
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  let vv: setvar v
  let vx: setvar x
  let cN: class N
  let cP: class P
  assume neifval.1: |- X = U. J


  assert |- ( J e. Top -> ( ( nei ` J ) ` S ) C_ ~P X )

  proof
    cJ
    ctop
    wcel
    #
    vv
    cS
    cJ
    cnei
    cfv
    cfv
    #
    cX
    cpw
    #
    @0
    vv
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    @3
    cX
    wss
    @5
    cS
    cJ
    @3
    cX
    neifval.1
    neii1
    vv
    cX
    selpw
    sylibr
    ex
    ssrdv
end
