include "cmgp.mm"
include "cfv.mm"
include "c0g.mm"
include "cur.mm"
include "cv.mm"
include "cbs.mm"
include "wcel.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "eqid.mm"
include "opprmul.mm"
include "eqeq1i.mm"
include "anbi12ci.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "iotabii.mm"
include "opprbas.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "grpidval.mm"
include "3eqtr4i.mm"
include "ringidval.mm"
include "3eqtr4ri.mm"

theorem oppr1
  let cR: class R
  let c.1: class .1.
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprbas.1: |- O = ( oppR ` R )
  assume oppr1.2: |- .1. = ( 1r ` R )


  assert |- .1. = ( 1r ` O )

  proof
    cO
    cmgp
    cfv
    #
    c0g
    cfv
    #
    cR
    cmgp
    cfv
    #
    c0g
    cfv
    #
    cO
    cur
    cfv
    #
    c.1
    vx
    cv
    #
    cR
    cbs
    cfv
    #
    wcel
    #
    @5
    vy
    cv
    #
    cO
    cmulr
    cfv
    #
    co
    #
    @8
    wceq
    #
    @8
    @5
    @9
    co
    #
    @8
    wceq
    #
    wa
    #
    vy
    @6
    wral
    #
    wa
    #
    vx
    cio
    @7
    @5
    @8
    cR
    cmulr
    cfv
    #
    co
    #
    @8
    wceq
    #
    @8
    @5
    @17
    co
    #
    @8
    wceq
    #
    wa
    #
    vy
    @6
    wral
    #
    wa
    #
    vx
    cio
    @1
    @3
    @16
    @24
    vx
    @15
    @23
    @7
    @14
    @22
    vy
    @6
    @11
    @21
    @13
    @19
    @10
    @20
    @8
    @6
    cR
    @9
    @17
    cO
    @5
    @8
    @6
    eqid
    #
    @17
    eqid
    #
    opprbas.1
    @9
    eqid
    #
    opprmul
    eqeq1i
    @12
    @18
    @8
    @6
    cR
    @9
    @17
    cO
    @8
    @5
    @25
    @26
    opprbas.1
    @27
    opprmul
    eqeq1i
    anbi12ci
    ralbii
    anbi2i
    iotabii
    vy
    @6
    @9
    vx
    @0
    @1
    @6
    cO
    @0
    @0
    eqid
    #
    @6
    cR
    cO
    opprbas.1
    @25
    opprbas
    mgpbas
    cO
    @9
    @0
    @28
    @27
    mgpplusg
    @1
    eqid
    grpidval
    vy
    @6
    @17
    vx
    @2
    @3
    @6
    cR
    @2
    @2
    eqid
    #
    @25
    mgpbas
    cR
    @17
    @2
    @29
    @26
    mgpplusg
    @3
    eqid
    grpidval
    3eqtr4i
    cO
    @4
    @0
    @28
    @4
    eqid
    ringidval
    cR
    c.1
    @2
    @29
    oppr1.2
    ringidval
    3eqtr4ri
end
