include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cmulr.mm"
include "wceq.mm"
include "ringidcl.mm"
include "eqid.mm"
include "dvrval.mm"
include "sylan.mm"
include "ringinvcl.mm"
include "ringlidm.mm"
include "syldan.mm"
include "eqtr2d.mm"

theorem ringinvdv
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cX: class X
  assume ringinvdv.b: |- B = ( Base ` R )
  assume ringinvdv.u: |- U = ( Unit ` R )
  assume ringinvdv.d: |- ./ = ( /r ` R )
  assume ringinvdv.o: |- .1. = ( 1r ` R )
  assume ringinvdv.i: |- I = ( invr ` R )


  assert |- ( ( R e. Ring /\ X e. U ) -> ( I ` X ) = ( .1. ./ X ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cU
    wcel
    #
    wa
    c.1
    cX
    c.dv
    co
    #
    c.1
    cX
    cI
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @3
    @0
    c.1
    cB
    wcel
    @1
    @2
    @5
    wceq
    cB
    cR
    c.1
    ringinvdv.b
    ringinvdv.o
    ringidcl
    cB
    c.dv
    cR
    @4
    cU
    cI
    c.1
    cX
    ringinvdv.b
    @4
    eqid
    #
    ringinvdv.u
    ringinvdv.i
    ringinvdv.d
    dvrval
    sylan
    @0
    @1
    @3
    cB
    wcel
    @5
    @3
    wceq
    cB
    cR
    cU
    cI
    cX
    ringinvdv.u
    ringinvdv.i
    ringinvdv.b
    ringinvcl
    cB
    cR
    @4
    c.1
    @3
    ringinvdv.b
    @6
    ringinvdv.o
    ringlidm
    syldan
    eqtr2d
end
