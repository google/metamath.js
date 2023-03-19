include "cclm.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "clmmul.mm"
include "adantr.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "clmod.mm"
include "clmlmod.mm"
include "eqid.mm"
include "lmodvsass.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem clmvsass
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume clmvscl.v: |- V = ( Base ` W )
  assume clmvscl.f: |- F = ( Scalar ` W )
  assume clmvscl.s: |- .x. = ( .s ` W )
  assume clmvscl.k: |- K = ( Base ` F )


  assert |- ( ( W e. CMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) -> ( ( Q x. R ) .x. X ) = ( Q .x. ( R .x. X ) ) )

  proof
    cW
    cclm
    wcel
    #
    cQ
    cK
    wcel
    cR
    cK
    wcel
    cX
    cV
    wcel
    w3a
    #
    wa
    #
    cQ
    cR
    cmul
    co
    #
    cX
    c.x
    co
    cQ
    cR
    cF
    cmulr
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    cQ
    cR
    cX
    c.x
    co
    c.x
    co
    #
    @2
    @3
    @5
    cX
    c.x
    @2
    cmul
    @4
    cQ
    cR
    @0
    cmul
    @4
    wceq
    @1
    cF
    cW
    clmvscl.f
    clmmul
    adantr
    oveqd
    oveq1d
    @0
    cW
    clmod
    wcel
    @1
    @6
    @7
    wceq
    cW
    clmlmod
    cQ
    cR
    c.x
    @4
    cF
    cK
    cV
    cW
    cX
    clmvscl.v
    clmvscl.f
    clmvscl.s
    clmvscl.k
    @4
    eqid
    lmodvsass
    sylan
    eqtrd
end
