include "csubg.mm"
include "cfv.mm"
include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "cbs.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "w3a.mm"
include "eqid.mm"
include "opprbas.mm"
include "cplusg.mm"
include "oppradd.mm"
include "grpprop.mm"
include "biid.mm"
include "cin.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "ressbas.mm"
include "ax-mp.mm"
include "eqtr3i.mm"
include "ressplusg.mm"
include "eqtr3d.mm"
include "3anbi123i.mm"
include "issubg.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem opprsubg
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opprbas.1: |- O = ( oppR ` R )


  assert |- ( SubGrp ` R ) = ( SubGrp ` O )

  proof
    vx
    cR
    csubg
    cfv
    #
    cO
    csubg
    cfv
    #
    cR
    cgrp
    wcel
    #
    vx
    cv
    #
    cR
    cbs
    cfv
    #
    wss
    #
    cR
    @3
    cress
    co
    #
    cgrp
    wcel
    #
    w3a
    cO
    cgrp
    wcel
    #
    @5
    cO
    @3
    cress
    co
    #
    cgrp
    wcel
    #
    w3a
    @3
    @0
    wcel
    @3
    @1
    wcel
    @2
    @8
    @5
    @5
    @7
    @10
    cR
    cO
    @4
    cR
    cO
    opprbas.1
    @4
    eqid
    #
    opprbas
    #
    cR
    cplusg
    cfv
    #
    cR
    cO
    opprbas.1
    @13
    eqid
    #
    oppradd
    #
    grpprop
    @5
    biid
    @6
    @9
    @3
    @4
    cin
    #
    @6
    cbs
    cfv
    #
    @9
    cbs
    cfv
    #
    @3
    cvv
    wcel
    #
    @16
    @17
    wceq
    vx
    vex
    #
    @3
    @4
    @6
    cvv
    cR
    @6
    eqid
    #
    @11
    ressbas
    ax-mp
    @19
    @16
    @18
    wceq
    @20
    @3
    @4
    @9
    cvv
    cO
    @9
    eqid
    #
    @12
    ressbas
    ax-mp
    eqtr3i
    @19
    @6
    cplusg
    cfv
    #
    @9
    cplusg
    cfv
    #
    wceq
    @20
    @19
    @13
    @23
    @24
    @3
    @13
    cR
    @6
    cvv
    @21
    @14
    ressplusg
    @3
    @13
    cO
    @9
    cvv
    @22
    @15
    ressplusg
    eqtr3d
    ax-mp
    grpprop
    3anbi123i
    @4
    @3
    cR
    @11
    issubg
    @4
    @3
    cO
    @12
    issubg
    3bitr4i
    eqriv
end
