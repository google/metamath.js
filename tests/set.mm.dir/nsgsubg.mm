include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wb.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isnsg.mm"
include "simplbi.mm"

theorem nsgsubg
  let cS: class S
  let cG: class G
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.mi: class .-
  let c.pl: class .+
  let cX: class X


  assert |- ( S e. ( NrmSGrp ` G ) -> S e. ( SubGrp ` G ) )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    cS
    cG
    csubg
    cfv
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    cS
    wcel
    @1
    @0
    @2
    co
    cS
    wcel
    wb
    vy
    cG
    cbs
    cfv
    #
    wral
    vx
    @3
    wral
    vx
    vy
    @2
    cS
    cG
    @3
    @3
    eqid
    @2
    eqid
    isnsg
    simplbi
end
