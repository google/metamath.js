include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "biid.mm"
include "pm4.24.mm"
include "w3a.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cmulr.mm"
include "cur.mm"
include "eqid.mm"
include "lmodlema.mm"
include "simpld.mm"
include "simp1d.mm"
include "syl3anb.mm"

theorem lmodvscl
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume lmodvscl.v: |- V = ( Base ` W )
  assume lmodvscl.f: |- F = ( Scalar ` W )
  assume lmodvscl.s: |- .x. = ( .s ` W )
  assume lmodvscl.k: |- K = ( Base ` F )


  assert |- ( ( W e. LMod /\ R e. K /\ X e. V ) -> ( R .x. X ) e. V )

  proof
    cW
    clmod
    wcel
    #
    @0
    cR
    cK
    wcel
    #
    @1
    @1
    wa
    #
    cX
    cV
    wcel
    #
    @3
    @3
    wa
    #
    cR
    cX
    c.x
    co
    #
    cV
    wcel
    #
    @0
    biid
    @1
    pm4.24
    @3
    pm4.24
    @0
    @2
    @4
    w3a
    #
    @6
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
    @5
    @5
    @8
    co
    #
    wceq
    #
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
    @9
    wceq
    #
    @7
    @6
    @10
    @12
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
    @5
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
    @8
    @11
    cR
    cR
    c.x
    @13
    @14
    cF
    cK
    cV
    cW
    cX
    cX
    lmodvscl.v
    @8
    eqid
    lmodvscl.s
    lmodvscl.f
    lmodvscl.k
    @11
    eqid
    @13
    eqid
    @14
    eqid
    lmodlema
    simpld
    simp1d
    syl3anb
end
