include "cslmd.mm"
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
include "c0g.mm"
include "eqid.mm"
include "slmdlema.mm"
include "simpld.mm"
include "simp1d.mm"
include "syl3anb.mm"

theorem slmdvscl
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume slmdvscl.v: |- V = ( Base ` W )
  assume slmdvscl.f: |- F = ( Scalar ` W )
  assume slmdvscl.s: |- .x. = ( .s ` W )
  assume slmdvscl.k: |- K = ( Base ` F )


  assert |- ( ( W e. SLMod /\ R e. K /\ X e. V ) -> ( R .x. X ) e. V )

  proof
    cW
    cslmd
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
    @8
    @11
    cR
    cR
    c.x
    @13
    @14
    cF
    cK
    @15
    cV
    cW
    cX
    cX
    @16
    slmdvscl.v
    @8
    eqid
    slmdvscl.s
    @16
    eqid
    slmdvscl.f
    slmdvscl.k
    @11
    eqid
    @13
    eqid
    @14
    eqid
    @15
    eqid
    slmdlema
    simpld
    simp1d
    syl3anb
end
