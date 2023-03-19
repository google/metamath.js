include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "cplusg.mm"
include "cminusg.mm"
include "cgrp.mm"
include "c0g.mm"
include "eqid.mm"
include "subgrcl.mm"
include "subgss.mm"
include "cv.mm"
include "subgcl.mm"
include "subg0cl.mm"
include "subginvcl.mm"
include "mulgsubcl.mm"

theorem subgmulgcl
  let cS: class S
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume subgmulgcl.t: |- .x. = ( .g ` G )


  assert |- ( ( S e. ( SubGrp ` G ) /\ N e. ZZ /\ X e. S ) -> ( N .x. X ) e. S )

  proof
    cS
    cG
    csubg
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
    c.x
    cG
    cG
    cminusg
    cfv
    #
    cN
    cgrp
    cX
    cG
    c0g
    cfv
    #
    @0
    eqid
    #
    subgmulgcl.t
    @1
    eqid
    #
    cS
    cG
    subgrcl
    @0
    cS
    cG
    @4
    subgss
    @1
    cS
    cG
    vx
    cv
    #
    vy
    cv
    @5
    subgcl
    @3
    eqid
    #
    cS
    cG
    @3
    @7
    subg0cl
    @2
    eqid
    #
    cS
    cG
    @2
    @6
    @8
    subginvcl
    mulgsubcl
end
