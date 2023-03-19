include "ccrg.mm"
include "wcel.mm"
include "wbr.mm"
include "coppr.mm"
include "cfv.mm"
include "cdsr.mm"
include "wa.mm"
include "cbs.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "crngoppr.mm"
include "3expa.mm"
include "eqcomd.mm"
include "an32s.mm"
include "eqeq1d.mm"
include "rexbidva.mm"
include "pm5.32da.mm"
include "opprbas.mm"
include "dvdsr.mm"
include "3bitr4g.mm"
include "anbi2d.mm"
include "isunit.mm"
include "pm4.24.mm"

theorem crngunit
  let c.pa: class .||
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cX: class X
  let vy: setvar y
  assume crngunit.1: |- U = ( Unit ` R )
  assume crngunit.2: |- .1. = ( 1r ` R )
  assume crngunit.3: |- .|| = ( ||r ` R )


  assert |- ( R e. CRing -> ( X e. U <-> X .|| .1. ) )

  proof
    cR
    ccrg
    wcel
    #
    cX
    c.1
    c.pa
    wbr
    #
    cX
    c.1
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    wa
    @1
    @1
    wa
    cX
    cU
    wcel
    @1
    @0
    @4
    @1
    @1
    @0
    cX
    cR
    cbs
    cfv
    #
    wcel
    #
    vy
    cv
    #
    cX
    @2
    cmulr
    cfv
    #
    co
    #
    c.1
    wceq
    #
    vy
    @5
    wrex
    #
    wa
    @6
    @7
    cX
    cR
    cmulr
    cfv
    #
    co
    #
    c.1
    wceq
    #
    vy
    @5
    wrex
    #
    wa
    @4
    @1
    @0
    @6
    @11
    @15
    @0
    @6
    wa
    #
    @10
    @14
    vy
    @5
    @16
    @7
    @5
    wcel
    #
    wa
    @9
    @13
    c.1
    @0
    @17
    @6
    @9
    @13
    wceq
    @0
    @17
    wa
    @6
    wa
    @13
    @9
    @0
    @17
    @6
    @13
    @9
    wceq
    @5
    cR
    @8
    @12
    @2
    @7
    cX
    @5
    eqid
    #
    @12
    eqid
    #
    @2
    eqid
    #
    @8
    eqid
    #
    crngoppr
    3expa
    eqcomd
    an32s
    eqeq1d
    rexbidva
    pm5.32da
    vy
    @5
    @3
    @2
    @8
    cX
    c.1
    @5
    cR
    @2
    @20
    @18
    opprbas
    @3
    eqid
    #
    @21
    dvdsr
    vy
    @5
    c.pa
    cR
    @12
    cX
    c.1
    @18
    crngunit.3
    @19
    dvdsr
    3bitr4g
    anbi2d
    c.pa
    cR
    @2
    cU
    c.1
    @3
    cX
    crngunit.1
    crngunit.2
    crngunit.3
    @20
    @22
    isunit
    @1
    pm4.24
    3bitr4g
end
