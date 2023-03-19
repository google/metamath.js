include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "c0g.mm"
include "eqid.mm"
include "grpidval.mm"
include "opprbas.mm"
include "oppradd.mm"
include "eqtr4i.mm"

theorem oppr0
  let cR: class R
  let cO: class O
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprbas.1: |- O = ( oppR ` R )
  assume oppr0.2: |- .0. = ( 0g ` R )


  assert |- .0. = ( 0g ` O )

  proof
    c.0
    vy
    cv
    #
    cR
    cbs
    cfv
    #
    wcel
    @0
    vx
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    @2
    wceq
    @2
    @0
    @3
    co
    @2
    wceq
    wa
    vx
    @1
    wral
    wa
    vy
    cio
    cO
    c0g
    cfv
    #
    vx
    @1
    @3
    vy
    cR
    c.0
    @1
    eqid
    #
    @3
    eqid
    #
    oppr0.2
    grpidval
    vx
    @1
    @3
    vy
    cO
    @4
    @1
    cR
    cO
    opprbas.1
    @5
    opprbas
    @3
    cR
    cO
    opprbas.1
    @6
    oppradd
    @4
    eqid
    grpidval
    eqtr4i
end
