include "clmod.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cmulr.mm"
include "cfv.mm"
include "cur.mm"
include "eqid.mm"
include "lmodlema.mm"
include "simpld.mm"
include "simp3d.mm"
include "3expa.mm"
include "anabsan2.mm"
include "exp42.mm"
include "3imp2.mm"

theorem lmodvsdir
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
  assume lmodvsdir.v: |- V = ( Base ` W )
  assume lmodvsdir.a: |- .+ = ( +g ` W )
  assume lmodvsdir.f: |- F = ( Scalar ` W )
  assume lmodvsdir.s: |- .x. = ( .s ` W )
  assume lmodvsdir.k: |- K = ( Base ` F )
  assume lmodvsdir.p: |- .+^ = ( +g ` F )


  assert |- ( ( W e. LMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) -> ( ( Q .+^ R ) .x. X ) = ( ( Q .x. X ) .+ ( R .x. X ) ) )

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
    wa
    c.pl
    c.pd
    cQ
    cR
    c.x
    @11
    @12
    cF
    cK
    cV
    cW
    cX
    cX
    lmodvsdir.v
    lmodvsdir.a
    lmodvsdir.s
    lmodvsdir.f
    lmodvsdir.k
    lmodvsdir.p
    @11
    eqid
    @12
    eqid
    lmodlema
    simpld
    simp3d
    3expa
    anabsan2
    exp42
    3imp2
end
