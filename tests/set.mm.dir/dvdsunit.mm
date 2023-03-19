include "ccrg.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "crg.mm"
include "wi.mm"
include "crngring.mm"
include "cbs.mm"
include "eqid.mm"
include "dvdsrtr.mm"
include "3expia.mm"
include "sylan.mm"
include "wb.mm"
include "crngunit.mm"
include "adantr.mm"
include "3imtr4d.mm"
include "3impia.mm"

theorem dvdsunit
  let c.pa: class .||
  let cR: class R
  let cU: class U
  let cX: class X
  let cY: class Y
  assume dvdsunit.1: |- U = ( Unit ` R )
  assume dvdsunit.3: |- .|| = ( ||r ` R )


  assert |- ( ( R e. CRing /\ Y .|| X /\ X e. U ) -> Y e. U )

  proof
    cR
    ccrg
    wcel
    #
    cY
    cX
    c.pa
    wbr
    #
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    @0
    @1
    wa
    cX
    cR
    cur
    cfv
    #
    c.pa
    wbr
    #
    cY
    @4
    c.pa
    wbr
    #
    @2
    @3
    @0
    cR
    crg
    wcel
    #
    @1
    @5
    @6
    wi
    cR
    crngring
    @7
    @1
    @5
    @6
    cR
    cbs
    cfv
    #
    c.pa
    cR
    @4
    cY
    cX
    @8
    eqid
    dvdsunit.3
    dvdsrtr
    3expia
    sylan
    @0
    @2
    @5
    wb
    @1
    c.pa
    cR
    cU
    @4
    cX
    dvdsunit.1
    @4
    eqid
    #
    dvdsunit.3
    crngunit
    adantr
    @0
    @3
    @6
    wb
    @1
    c.pa
    cR
    cU
    @4
    cY
    dvdsunit.1
    @9
    dvdsunit.3
    crngunit
    adantr
    3imtr4d
    3impia
end
