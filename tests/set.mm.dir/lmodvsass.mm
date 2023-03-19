include "clmod.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cplusg.mm"
include "cfv.mm"
include "cur.mm"
include "eqid.mm"
include "lmodlema.mm"
include "simprld.mm"
include "3expa.mm"
include "anabsan2.mm"
include "exp42.mm"
include "3imp2.mm"

theorem lmodvsass
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume lmodvsass.v: |- V = ( Base ` W )
  assume lmodvsass.f: |- F = ( Scalar ` W )
  assume lmodvsass.s: |- .x. = ( .s ` W )
  assume lmodvsass.k: |- K = ( Base ` F )
  assume lmodvsass.t: |- .X. = ( .r ` F )


  assert |- ( ( W e. LMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) -> ( ( Q .X. R ) .x. X ) = ( Q .x. ( R .x. X ) ) )

  proof
    cW
    clmod
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
    @8
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
    @8
    co
    wceq
    w3a
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
    @8
    @9
    cQ
    cR
    c.x
    c.xp
    @10
    cF
    cK
    cV
    cW
    cX
    cX
    lmodvsass.v
    @8
    eqid
    lmodvsass.s
    lmodvsass.f
    lmodvsass.k
    @9
    eqid
    lmodvsass.t
    @10
    eqid
    lmodlema
    simprld
    3expa
    anabsan2
    exp42
    3imp2
end
