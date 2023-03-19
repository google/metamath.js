include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "wceq.mm"
include "eqid.mm"
include "dvrval.mm"
include "3adant1.mm"
include "ringinvcl.mm"
include "3adant2.mm"
include "ringcl.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem dvrcl
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cU: class U
  let cX: class X
  let cY: class Y
  assume dvrcl.b: |- B = ( Base ` R )
  assume dvrcl.o: |- U = ( Unit ` R )
  assume dvrcl.d: |- ./ = ( /r ` R )


  assert |- ( ( R e. Ring /\ X e. B /\ Y e. U ) -> ( X ./ Y ) e. B )

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
    cB
    @1
    @2
    @3
    @7
    wceq
    @0
    cB
    c.dv
    cR
    @6
    cU
    @4
    cX
    cY
    dvrcl.b
    @6
    eqid
    #
    dvrcl.o
    @4
    eqid
    #
    dvrcl.d
    dvrval
    3adant1
    @0
    @1
    @2
    @5
    cB
    wcel
    #
    @7
    cB
    wcel
    @0
    @2
    @10
    @1
    cB
    cR
    cU
    @4
    cY
    dvrcl.o
    @9
    dvrcl.b
    ringinvcl
    3adant2
    cB
    cR
    @6
    cX
    @5
    dvrcl.b
    @8
    ringcl
    syld3an3
    eqeltrd
end
