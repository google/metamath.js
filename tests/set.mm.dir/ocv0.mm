include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "0ss.mm"
include "eqid.mm"
include "ocvval.mm"
include "ax-mp.mm"
include "ral0.mm"
include "rgenw.mm"
include "rabid2.mm"
include "mpbir.mm"
include "eqtr4i.mm"

theorem ocv0
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume ocvz.v: |- V = ( Base ` W )
  assume ocvz.o: |- ._|_ = ( ocv ` W )


  assert |- ( ._|_ ` (/) ) = V

  proof
    c0
    c.pe
    cfv
    #
    vx
    cv
    vy
    cv
    cW
    cip
    cfv
    #
    co
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vy
    c0
    wral
    #
    vx
    cV
    crab
    #
    cV
    c0
    cV
    wss
    @0
    @6
    wceq
    cV
    0ss
    vx
    vy
    c0
    @2
    @1
    c.pe
    cV
    cW
    @3
    ocvz.v
    @1
    eqid
    @2
    eqid
    @3
    eqid
    ocvz.o
    ocvval
    ax-mp
    cV
    @6
    wceq
    @5
    vx
    cV
    wral
    @5
    vx
    cV
    @4
    vy
    ral0
    rgenw
    @5
    vx
    cV
    rabid2
    mpbir
    eqtr4i
end
