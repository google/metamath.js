include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmnd.mm"
include "c0g.mm"
include "eqid.mm"
include "submrcl.mm"
include "submss.mm"
include "cv.mm"
include "submcl.mm"
include "subm0cl.mm"
include "mulgnn0subcl.mm"

theorem submmulgcl
  let cS: class S
  let c.xb: class .xb
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume submmulgcl.t: |- .xb = ( .g ` G )


  assert |- ( ( S e. ( SubMnd ` G ) /\ N e. NN0 /\ X e. S ) -> ( N .xb X ) e. S )

  proof
    cS
    cG
    csubmnd
    cfv
    wcel
    vx
    vy
    cG
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    cS
    c.xb
    cG
    cN
    cmnd
    cX
    cG
    c0g
    cfv
    #
    @0
    eqid
    #
    submmulgcl.t
    @1
    eqid
    #
    cS
    cG
    submrcl
    @0
    cS
    cG
    @3
    submss
    @1
    cS
    cG
    vx
    cv
    vy
    cv
    @4
    submcl
    @2
    eqid
    #
    cS
    cG
    @2
    @5
    subm0cl
    mulgnn0subcl
end
