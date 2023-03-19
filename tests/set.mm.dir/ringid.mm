include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cur.mm"
include "cfv.mm"
include "eqid.mm"
include "ringidcl.mm"
include "adantr.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "adantl.mm"
include "ringidmlem.mm"
include "rspcedvd.mm"

theorem ringid
  let vu: setvar u
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  assume ringid.b: |- B = ( Base ` R )
  assume ringid.t: |- .x. = ( .r ` R )

  disjoint B u
  disjoint R u
  disjoint X u
  disjoint .x. u
  assert |- ( ( R e. Ring /\ X e. B ) -> E. u e. B ( ( u .x. X ) = X /\ ( X .x. u ) = X ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    vu
    cv
    #
    cX
    c.x
    co
    #
    cX
    wceq
    #
    cX
    @3
    c.x
    co
    #
    cX
    wceq
    #
    wa
    #
    cR
    cur
    cfv
    #
    cX
    c.x
    co
    #
    cX
    wceq
    #
    cX
    @9
    c.x
    co
    #
    cX
    wceq
    #
    wa
    #
    vu
    @9
    cB
    @0
    @9
    cB
    wcel
    @1
    cB
    cR
    @9
    ringid.b
    @9
    eqid
    #
    ringidcl
    adantr
    @3
    @9
    wceq
    #
    @8
    @14
    wb
    @2
    @16
    @5
    @11
    @7
    @13
    @16
    @4
    @10
    cX
    @3
    @9
    cX
    c.x
    oveq1
    eqeq1d
    @16
    @6
    @12
    cX
    @3
    @9
    cX
    c.x
    oveq2
    eqeq1d
    anbi12d
    adantl
    cB
    cR
    c.x
    @9
    cX
    ringid.b
    ringid.t
    @15
    ringidmlem
    rspcedvd
end
