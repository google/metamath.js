include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "eqid.mm"
include "unitrinv.mm"
include "cbs.mm"
include "ringinvcl.mm"
include "ringlz.mm"
include "syldan.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "1unit.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "impbida.mm"

theorem 0unit
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let c.0: class .0.
  assume 0unit.1: |- U = ( Unit ` R )
  assume 0unit.2: |- .0. = ( 0g ` R )
  assume 0unit.3: |- .1. = ( 1r ` R )


  assert |- ( R e. Ring -> ( .0. e. U <-> .1. = .0. ) )

  proof
    cR
    crg
    wcel
    #
    c.0
    cU
    wcel
    #
    c.1
    c.0
    wceq
    #
    @0
    @1
    wa
    c.0
    c.0
    cR
    cinvr
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    c.1
    c.0
    cR
    @5
    cU
    c.1
    @3
    c.0
    0unit.1
    @3
    eqid
    #
    @5
    eqid
    #
    0unit.3
    unitrinv
    @0
    @1
    @4
    cR
    cbs
    cfv
    #
    wcel
    @6
    c.0
    wceq
    @9
    cR
    cU
    @3
    c.0
    0unit.1
    @7
    @9
    eqid
    #
    ringinvcl
    @9
    cR
    @5
    @4
    c.0
    @10
    @8
    0unit.2
    ringlz
    syldan
    eqtr3d
    @0
    @2
    wa
    c.1
    c.0
    cU
    @0
    @2
    simpr
    @0
    c.1
    cU
    wcel
    @2
    cR
    cU
    c.1
    0unit.1
    0unit.3
    1unit
    adantr
    eqeltrrd
    impbida
end
