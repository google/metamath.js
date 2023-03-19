include "clmod.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "cplusg.mm"
include "cfv.mm"
include "cmulr.mm"
include "cur.mm"
include "eqid.mm"
include "lmodlema.mm"
include "simpld.mm"
include "simp2d.mm"
include "3expia.mm"
include "anabsan2.mm"
include "exp4b.mm"
include "com34.mm"
include "3imp2.mm"

theorem lmodvsdi
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lmodvsdi.v: |- V = ( Base ` W )
  assume lmodvsdi.a: |- .+ = ( +g ` W )
  assume lmodvsdi.f: |- F = ( Scalar ` W )
  assume lmodvsdi.s: |- .x. = ( .s ` W )
  assume lmodvsdi.k: |- K = ( Base ` F )


  assert |- ( ( W e. LMod /\ ( R e. K /\ X e. V /\ Y e. V ) ) -> ( R .x. ( X .+ Y ) ) = ( ( R .x. X ) .+ ( R .x. Y ) ) )

  proof
    cW
    clmod
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
    cY
    cV
    wcel
    #
    cR
    cX
    cY
    c.pl
    co
    c.x
    co
    cR
    cX
    c.x
    co
    #
    cR
    cY
    c.x
    co
    c.pl
    co
    wceq
    #
    @0
    @1
    @3
    @2
    @5
    @0
    @1
    @3
    @2
    @5
    @0
    @1
    @3
    @2
    wa
    #
    @5
    wi
    @0
    @1
    @1
    wa
    #
    @6
    @5
    @0
    @7
    @6
    w3a
    #
    @4
    cV
    wcel
    #
    @5
    cR
    cR
    cF
    cplusg
    cfv
    #
    co
    cX
    c.x
    co
    @4
    @4
    c.pl
    co
    wceq
    #
    @8
    @9
    @5
    @11
    w3a
    cR
    cR
    cF
    cmulr
    cfv
    #
    co
    cX
    c.x
    co
    cR
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
    wa
    c.pl
    @10
    cR
    cR
    c.x
    @12
    @13
    cF
    cK
    cV
    cW
    cY
    cX
    lmodvsdi.v
    lmodvsdi.a
    lmodvsdi.s
    lmodvsdi.f
    lmodvsdi.k
    @10
    eqid
    @12
    eqid
    @13
    eqid
    lmodlema
    simpld
    simp2d
    3expia
    anabsan2
    exp4b
    com34
    3imp2
end
