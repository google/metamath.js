include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "crio.mm"
include "riotaex.mm"
include "eqid.mm"
include "grpinvfval.mm"
include "fnmpti.mm"

theorem grpinvfn
  let cB: class B
  let cG: class G
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume grpinvfn.b: |- B = ( Base ` G )
  assume grpinvfn.n: |- N = ( invg ` G )


  assert |- N Fn B

  proof
    vx
    cB
    vy
    cv
    vx
    cv
    cG
    cplusg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    wceq
    #
    vy
    cB
    crio
    cN
    @2
    vy
    cB
    riotaex
    vx
    vy
    cB
    @0
    cG
    cN
    @1
    grpinvfn.b
    @0
    eqid
    @1
    eqid
    grpinvfn.n
    grpinvfval
    fnmpti
end
