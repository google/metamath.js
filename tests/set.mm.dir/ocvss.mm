include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "eqid.mm"
include "elocv.mm"
include "simp2bi.mm"
include "ssriv.mm"

theorem ocvss
  let cS: class S
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ocvss.v: |- V = ( Base ` W )
  assume ocvss.o: |- ._|_ = ( ocv ` W )


  assert |- ( ._|_ ` S ) C_ V

  proof
    vx
    cS
    c.pe
    cfv
    #
    cV
    vx
    cv
    #
    @0
    wcel
    cS
    cV
    wss
    @1
    cV
    wcel
    @1
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
    vy
    cS
    wral
    vy
    @1
    cS
    @3
    @2
    c.pe
    cV
    cW
    @4
    ocvss.v
    @2
    eqid
    @3
    eqid
    @4
    eqid
    ocvss.o
    elocv
    simp2bi
    ssriv
end
