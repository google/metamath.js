include "cslmd.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cmulr.mm"
include "cfv.mm"
include "cur.mm"
include "c0g.mm"
include "eqid.mm"
include "slmdlema.mm"
include "simpld.mm"
include "simp3d.mm"
include "3expa.mm"
include "anabsan2.mm"
include "exp42.mm"
include "3imp2.mm"

theorem slmdvsdir
  let c.pl: class .+
  let c.pd: class .+^
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume slmdvsdir.v: |- V = ( Base ` W )
  assume slmdvsdir.a: |- .+ = ( +g ` W )
  assume slmdvsdir.f: |- F = ( Scalar ` W )
  assume slmdvsdir.s: |- .x. = ( .s ` W )
  assume slmdvsdir.k: |- K = ( Base ` F )
  assume slmdvsdir.p: |- .+^ = ( +g ` F )


  assert |- ( ( W e. SLMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) -> ( ( Q .+^ R ) .x. X ) = ( ( Q .x. X ) .+ ( R .x. X ) ) )

  proof
    cW
    cslmd
    wcel
    #
    cQ
    cK
    wcel
    #
    cR
    cK
    wcel
    #
    cX
    cV
    wcel
    #
    cQ
    cR
    c.pd
    co
    cX
    c.x
    co
    cQ
    cX
    c.x
    co
    cR
    cX
    c.x
    co
    #
    c.pl
    co
    wceq
    #
    @0
    @1
    @2
    @3
    @5
    @0
    @1
    @2
    wa
    #
    wa
    @3
    @5
    @0
    @6
    @3
    @3
    wa
    #
    @5
    @0
    @6
    @7
    w3a
    #
    @4
    cV
    wcel
    #
    cR
    cX
    cX
    c.pl
    co
    c.x
    co
    @4
    @4
    c.pl
    co
    wceq
    #
    @5
    @8
    @9
    @10
    @5
    w3a
    cQ
    cR
    cF
    cmulr
    cfv
    #
    co
    cX
    c.x
    co
    cQ
    @4
    c.x
    co
    wceq
    cF
    cur
    cfv
    #
    cX
    c.x
    co
    cX
    wceq
    cF
    c0g
    cfv
    #
    cX
    c.x
    co
    cW
    c0g
    cfv
    #
    wceq
    w3a
    c.pl
    c.pd
    cQ
    cR
    c.x
    @11
    @12
    cF
    cK
    @13
    cV
    cW
    cX
    cX
    @14
    slmdvsdir.v
    slmdvsdir.a
    slmdvsdir.s
    @14
    eqid
    slmdvsdir.f
    slmdvsdir.k
    slmdvsdir.p
    @11
    eqid
    @12
    eqid
    @13
    eqid
    slmdlema
    simpld
    simp3d
    3expa
    anabsan2
    exp42
    3imp2
end
