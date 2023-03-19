include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "eqid.mm"
include "rrgval.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem rrgss
  let cB: class B
  let cR: class R
  let cE: class E
  let vx: setvar x
  let vy: setvar y
  assume rrgss.e: |- E = ( RLReg ` R )
  assume rrgss.b: |- B = ( Base ` R )


  assert |- E C_ B

  proof
    cE
    vx
    cv
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    cR
    c0g
    cfv
    #
    wceq
    @0
    @2
    wceq
    wi
    vy
    cB
    wral
    #
    vx
    cB
    crab
    cB
    vx
    vy
    cB
    cR
    @1
    cE
    @2
    rrgss.e
    rrgss.b
    @1
    eqid
    @2
    eqid
    rrgval
    @3
    vx
    cB
    ssrab2
    eqsstri
end
