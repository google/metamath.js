include "cslmd.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "cplusg.mm"
include "eqid.mm"
include "slmdlema.mm"
include "simprd.mm"
include "simp1d.mm"
include "3expa.mm"
include "anabsan2.mm"
include "exp42.mm"
include "3imp2.mm"

theorem slmdvsass
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume slmdvsass.v: |- V = ( Base ` W )
  assume slmdvsass.f: |- F = ( Scalar ` W )
  assume slmdvsass.s: |- .x. = ( .s ` W )
  assume slmdvsass.k: |- K = ( Base ` F )
  assume slmdvsass.t: |- .X. = ( .r ` F )


  assert |- ( ( W e. SLMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) -> ( ( Q .X. R ) .x. X ) = ( Q .x. ( R .x. X ) ) )

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
    c.xp
    co
    cX
    c.x
    co
    cQ
    cR
    cX
    c.x
    co
    #
    c.x
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
    @5
    cF
    cur
    cfv
    #
    cX
    c.x
    co
    cX
    wceq
    #
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
    #
    @8
    @4
    cV
    wcel
    cR
    cX
    cX
    cW
    cplusg
    cfv
    #
    co
    c.x
    co
    @4
    @4
    @14
    co
    wceq
    cQ
    cR
    cF
    cplusg
    cfv
    #
    co
    cX
    c.x
    co
    cQ
    cX
    c.x
    co
    @4
    @14
    co
    wceq
    w3a
    @5
    @10
    @13
    w3a
    @14
    @15
    cQ
    cR
    c.x
    c.xp
    @9
    cF
    cK
    @11
    cV
    cW
    cX
    cX
    @12
    slmdvsass.v
    @14
    eqid
    slmdvsass.s
    @12
    eqid
    slmdvsass.f
    slmdvsass.k
    @15
    eqid
    slmdvsass.t
    @9
    eqid
    @11
    eqid
    slmdlema
    simprd
    simp1d
    3expa
    anabsan2
    exp42
    3imp2
end
