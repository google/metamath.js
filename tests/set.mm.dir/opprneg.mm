include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt.mm"
include "cminusg.mm"
include "eqid.mm"
include "grpinvfval.mm"
include "opprbas.mm"
include "oppradd.mm"
include "oppr0.mm"
include "eqtr4i.mm"

theorem opprneg
  let cR: class R
  let cN: class N
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprbas.1: |- O = ( oppR ` R )
  assume opprneg.2: |- N = ( invg ` R )


  assert |- N = ( invg ` O )

  proof
    cN
    vx
    cR
    cbs
    cfv
    #
    vy
    cv
    vx
    cv
    cR
    cplusg
    cfv
    #
    co
    cR
    c0g
    cfv
    #
    wceq
    vy
    @0
    crio
    cmpt
    cO
    cminusg
    cfv
    #
    vx
    vy
    @0
    @1
    cR
    cN
    @2
    @0
    eqid
    #
    @1
    eqid
    #
    @2
    eqid
    #
    opprneg.2
    grpinvfval
    vx
    vy
    @0
    @1
    cO
    @3
    @2
    @0
    cR
    cO
    opprbas.1
    @4
    opprbas
    @1
    cR
    cO
    opprbas.1
    @5
    oppradd
    cR
    cO
    @2
    opprbas.1
    @6
    oppr0
    @3
    eqid
    grpinvfval
    eqtr4i
end
