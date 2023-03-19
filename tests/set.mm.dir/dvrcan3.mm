include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cur.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "unitcl.mm"
include "3ad2ant3.mm"
include "simp3.mm"
include "dvrass.mm"
include "syl13anc.mm"
include "eqid.mm"
include "dvrid.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "3adant3.mm"
include "3eqtrd.mm"

theorem dvrcan3
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


  assert |- ( ( R e. Ring /\ X e. B /\ Y e. U ) -> ( ( X .x. Y ) ./ Y ) = X )

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
    c.x
    co
    cY
    c.dv
    co
    #
    cX
    cY
    cY
    c.dv
    co
    #
    c.x
    co
    #
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
    @0
    @1
    cY
    cB
    wcel
    #
    @2
    @4
    @6
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @2
    @0
    @9
    @1
    cB
    cR
    cU
    cY
    dvrass.b
    dvrass.o
    unitcl
    3ad2ant3
    @0
    @1
    @2
    simp3
    cB
    c.dv
    cR
    c.x
    cU
    cX
    cY
    cY
    dvrass.b
    dvrass.o
    dvrass.d
    dvrass.t
    dvrass
    syl13anc
    @3
    @5
    @7
    cX
    c.x
    @0
    @2
    @5
    @7
    wceq
    @1
    c.dv
    cR
    cU
    @7
    cY
    dvrass.o
    dvrass.d
    @7
    eqid
    #
    dvrid
    3adant2
    oveq2d
    @0
    @1
    @8
    cX
    wceq
    @2
    cB
    cR
    c.x
    @7
    cX
    dvrass.b
    dvrass.t
    @10
    ringridm
    3adant3
    3eqtrd
end
