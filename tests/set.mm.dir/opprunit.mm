include "cui.mm"
include "cfv.mm"
include "cv.mm"
include "cur.mm"
include "cdsr.mm"
include "wbr.mm"
include "wa.mm"
include "coppr.mm"
include "wcel.mm"
include "cbs.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "opprbas.mm"
include "opprmul.mm"
include "eqtr2i.mm"
include "eqeq1i.mm"
include "rexbii.mm"
include "anbi2i.mm"
include "dvdsr.mm"
include "3bitr4i.mm"
include "anbi2ci.mm"
include "isunit.mm"
include "oppr1.mm"
include "eqriv.mm"

theorem opprunit
  let cR: class R
  let cS: class S
  let cU: class U
  let vy: setvar y
  let vx: setvar x
  assume opprunit.1: |- U = ( Unit ` R )
  assume opprunit.2: |- S = ( oppR ` R )


  assert |- U = ( Unit ` S )

  proof
    vx
    cU
    cS
    cui
    cfv
    #
    vx
    cv
    #
    cR
    cur
    cfv
    #
    cR
    cdsr
    cfv
    #
    wbr
    #
    @1
    @2
    cS
    cdsr
    cfv
    #
    wbr
    #
    wa
    @6
    @1
    @2
    cS
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
    cU
    wcel
    @1
    @0
    wcel
    @4
    @9
    @6
    @1
    cR
    cbs
    cfv
    #
    wcel
    #
    vy
    cv
    #
    @1
    cR
    cmulr
    cfv
    #
    co
    #
    @2
    wceq
    #
    vy
    @10
    wrex
    #
    wa
    @11
    @12
    @1
    @7
    cmulr
    cfv
    #
    co
    #
    @2
    wceq
    #
    vy
    @10
    wrex
    #
    wa
    @4
    @9
    @16
    @20
    @11
    @15
    @19
    vy
    @10
    @14
    @18
    @2
    @18
    @1
    @12
    cS
    cmulr
    cfv
    #
    co
    @14
    @10
    cS
    @17
    @21
    @7
    @12
    @1
    @10
    cR
    cS
    opprunit.2
    @10
    eqid
    #
    opprbas
    #
    @21
    eqid
    #
    @7
    eqid
    #
    @17
    eqid
    #
    opprmul
    @10
    cR
    @21
    @13
    cS
    @1
    @12
    @22
    @13
    eqid
    #
    opprunit.2
    @24
    opprmul
    eqtr2i
    eqeq1i
    rexbii
    anbi2i
    vy
    @10
    @3
    cR
    @13
    @1
    @2
    @22
    @3
    eqid
    #
    @27
    dvdsr
    vy
    @10
    @8
    @7
    @17
    @1
    @2
    @10
    cS
    @7
    @25
    @23
    opprbas
    @8
    eqid
    #
    @26
    dvdsr
    3bitr4i
    anbi2ci
    @3
    cR
    cS
    cU
    @2
    @5
    @1
    opprunit.1
    @2
    eqid
    #
    @28
    opprunit.2
    @5
    eqid
    #
    isunit
    @5
    cS
    @7
    @0
    @2
    @8
    @1
    @0
    eqid
    cR
    @2
    cS
    opprunit.2
    @30
    oppr1
    @31
    @25
    @29
    isunit
    3bitr4i
    eqriv
end
