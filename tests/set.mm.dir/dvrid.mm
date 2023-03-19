include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "unitcl.mm"
include "adantl.mm"
include "dvrval.mm"
include "sylancom.mm"
include "unitrinv.mm"
include "eqtrd.mm"

theorem dvrid
  let c.dv: class ./
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cX: class X
  assume unitdvcl.o: |- U = ( Unit ` R )
  assume unitdvcl.d: |- ./ = ( /r ` R )
  assume dvrid.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ X e. U ) -> ( X ./ X ) = .1. )

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
    cX
    cX
    c.dv
    co
    #
    cX
    cX
    cR
    cinvr
    cfv
    #
    cfv
    cR
    cmulr
    cfv
    #
    co
    #
    c.1
    @0
    @1
    cX
    cR
    cbs
    cfv
    #
    wcel
    #
    @2
    @5
    wceq
    @1
    @7
    @0
    @6
    cR
    cU
    cX
    @6
    eqid
    #
    unitdvcl.o
    unitcl
    adantl
    @6
    c.dv
    cR
    @4
    cU
    @3
    cX
    cX
    @8
    @4
    eqid
    #
    unitdvcl.o
    @3
    eqid
    #
    unitdvcl.d
    dvrval
    sylancom
    cR
    @4
    cU
    c.1
    @3
    cX
    unitdvcl.o
    @10
    @9
    dvrid.o
    unitrinv
    eqtrd
end
