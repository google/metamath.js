include "cclm.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "clmadd.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "adantr.mm"
include "clmod.mm"
include "clmlmod.mm"
include "eqid.mm"
include "lmodvsdir.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem clmvsdir
  let c.pl: class .+
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
  assume clmvsdir.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. CMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) -> ( ( Q + R ) .x. X ) = ( ( Q .x. X ) .+ ( R .x. X ) ) )

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
    cQ
    cR
    caddc
    co
    #
    cX
    c.x
    co
    #
    cQ
    cR
    cF
    cplusg
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    cQ
    cX
    c.x
    co
    cR
    cX
    c.x
    co
    c.pl
    co
    #
    @0
    @3
    @6
    wceq
    @1
    @0
    @2
    @5
    cX
    c.x
    @0
    caddc
    @4
    cQ
    cR
    cF
    cW
    clmvscl.f
    clmadd
    oveqd
    oveq1d
    adantr
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
    c.pl
    @4
    cQ
    cR
    c.x
    cF
    cK
    cV
    cW
    cX
    clmvscl.v
    clmvsdir.a
    clmvscl.f
    clmvscl.s
    clmvscl.k
    @4
    eqid
    lmodvsdir
    sylan
    eqtrd
end
