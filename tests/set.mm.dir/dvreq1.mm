include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cmulr.mm"
include "cfv.mm"
include "oveq1.mm"
include "eqid.mm"
include "dvrcan1.mm"
include "unitcl.mm"
include "ringlidm.mm"
include "sylan2.mm"
include "3adant2.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "dvrid.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem dvreq1
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cX: class X
  let cY: class Y
  assume dvreq1.b: |- B = ( Base ` R )
  assume dvreq1.o: |- U = ( Unit ` R )
  assume dvreq1.d: |- ./ = ( /r ` R )
  assume dvreq1.t: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ X e. B /\ Y e. U ) -> ( ( X ./ Y ) = .1. <-> X = Y ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cU
    wcel
    #
    w3a
    #
    cX
    cY
    c.dv
    co
    #
    c.1
    wceq
    #
    cX
    cY
    wceq
    #
    @5
    @4
    cY
    cR
    cmulr
    cfv
    #
    co
    #
    c.1
    cY
    @7
    co
    #
    wceq
    @3
    @6
    @4
    c.1
    cY
    @7
    oveq1
    @3
    @8
    cX
    @9
    cY
    cB
    c.dv
    cR
    @7
    cU
    cX
    cY
    dvreq1.b
    dvreq1.o
    dvreq1.d
    @7
    eqid
    #
    dvrcan1
    @0
    @2
    @9
    cY
    wceq
    #
    @1
    @2
    @0
    cY
    cB
    wcel
    @11
    cB
    cR
    cU
    cY
    dvreq1.b
    dvreq1.o
    unitcl
    cB
    cR
    @7
    c.1
    cY
    dvreq1.b
    @10
    dvreq1.t
    ringlidm
    sylan2
    3adant2
    eqeq12d
    syl5ib
    @3
    @5
    @6
    cY
    cY
    c.dv
    co
    #
    c.1
    wceq
    #
    @0
    @2
    @13
    @1
    c.dv
    cR
    cU
    c.1
    cY
    dvreq1.o
    dvreq1.d
    dvreq1.t
    dvrid
    3adant2
    @6
    @4
    @12
    c.1
    cX
    cY
    cY
    c.dv
    oveq1
    eqeq1d
    syl5ibrcom
    impbid
end
