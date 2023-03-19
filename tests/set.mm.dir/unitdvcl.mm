include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "unitcl.mm"
include "dvrval.mm"
include "sylan.mm"
include "3adant1.mm"
include "unitinvcl.mm"
include "3adant2.mm"
include "unitmulcl.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem unitdvcl
  let c.dv: class ./
  let cR: class R
  let cU: class U
  let cX: class X
  let cY: class Y
  assume unitdvcl.o: |- U = ( Unit ` R )
  assume unitdvcl.d: |- ./ = ( /r ` R )


  assert |- ( ( R e. Ring /\ X e. U /\ Y e. U ) -> ( X ./ Y ) e. U )

  proof
    cR
    crg
    wcel
    #
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    w3a
    cX
    cY
    c.dv
    co
    #
    cX
    cY
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
    cU
    @1
    @2
    @3
    @7
    wceq
    #
    @0
    @1
    cX
    cR
    cbs
    cfv
    #
    wcel
    @2
    @8
    @9
    cR
    cU
    cX
    @9
    eqid
    #
    unitdvcl.o
    unitcl
    @9
    c.dv
    cR
    @6
    cU
    @4
    cX
    cY
    @10
    @6
    eqid
    #
    unitdvcl.o
    @4
    eqid
    #
    unitdvcl.d
    dvrval
    sylan
    3adant1
    @0
    @1
    @2
    @5
    cU
    wcel
    #
    @7
    cU
    wcel
    @0
    @2
    @13
    @1
    cR
    cU
    @4
    cY
    unitdvcl.o
    @12
    unitinvcl
    3adant2
    cR
    @6
    cU
    cX
    @5
    unitdvcl.o
    @11
    unitmulcl
    syld3an3
    eqeltrd
end
