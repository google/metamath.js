include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "dvrval.mm"
include "3adant1.mm"
include "oveq1d.mm"
include "simp1.mm"
include "simp2.mm"
include "ringinvcl.mm"
include "3adant2.mm"
include "unitcl.mm"
include "3ad2ant3.mm"
include "ringass.mm"
include "syl13anc.mm"
include "cur.mm"
include "unitlinv.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "3adant3.mm"
include "eqtrd.mm"

theorem dvrcan1
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cX: class X
  let cY: class Y
  assume dvrass.b: |- B = ( Base ` R )
  assume dvrass.o: |- U = ( Unit ` R )
  assume dvrass.d: |- ./ = ( /r ` R )
  assume dvrass.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ X e. B /\ Y e. U ) -> ( ( X ./ Y ) .x. Y ) = X )

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
    cY
    c.x
    co
    cX
    cY
    cR
    cinvr
    cfv
    #
    cfv
    #
    c.x
    co
    #
    cY
    c.x
    co
    #
    cX
    @3
    @4
    @7
    cY
    c.x
    @1
    @2
    @4
    @7
    wceq
    @0
    cB
    c.dv
    cR
    c.x
    cU
    @5
    cX
    cY
    dvrass.b
    dvrass.t
    dvrass.o
    @5
    eqid
    #
    dvrass.d
    dvrval
    3adant1
    oveq1d
    @3
    @8
    cX
    @6
    cY
    c.x
    co
    #
    c.x
    co
    #
    cX
    @3
    @0
    @1
    @6
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @8
    @11
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @2
    @12
    @1
    cB
    cR
    cU
    @5
    cY
    dvrass.o
    @9
    dvrass.b
    ringinvcl
    3adant2
    @2
    @0
    @13
    @1
    cB
    cR
    cU
    cY
    dvrass.b
    dvrass.o
    unitcl
    3ad2ant3
    cB
    cR
    c.x
    cX
    @6
    cY
    dvrass.b
    dvrass.t
    ringass
    syl13anc
    @3
    @11
    cX
    cR
    cur
    cfv
    #
    c.x
    co
    #
    cX
    @3
    @10
    @14
    cX
    c.x
    @0
    @2
    @10
    @14
    wceq
    @1
    cR
    c.x
    cU
    @14
    @5
    cY
    dvrass.o
    @9
    dvrass.t
    @14
    eqid
    #
    unitlinv
    3adant2
    oveq2d
    @0
    @1
    @15
    cX
    wceq
    @2
    cB
    cR
    c.x
    @14
    cX
    dvrass.b
    dvrass.t
    @16
    ringridm
    3adant3
    eqtrd
    eqtrd
    eqtrd
end
