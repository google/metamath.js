include "cslmd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "eqid.mm"
include "slmd1cl.mm"
include "adantr.mm"
include "simpr.mm"
include "w3a.mm"
include "cmulr.mm"
include "c0g.mm"
include "cplusg.mm"
include "slmdlema.mm"
include "simprd.mm"
include "simp2d.mm"
include "syl122anc.mm"

theorem slmdvs1
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  assume slmdvs1.v: |- V = ( Base ` W )
  assume slmdvs1.f: |- F = ( Scalar ` W )
  assume slmdvs1.s: |- .x. = ( .s ` W )
  assume slmdvs1.u: |- .1. = ( 1r ` F )


  assert |- ( ( W e. SLMod /\ X e. V ) -> ( .1. .x. X ) = X )

  proof
    cW
    cslmd
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    @0
    c.1
    cF
    cbs
    cfv
    #
    wcel
    #
    @3
    @1
    @1
    c.1
    cX
    c.x
    co
    #
    cX
    wceq
    #
    @0
    @1
    simpl
    @0
    @3
    @1
    c.1
    cF
    @2
    cW
    slmdvs1.f
    @2
    eqid
    #
    slmdvs1.u
    slmd1cl
    adantr
    #
    @7
    @0
    @1
    simpr
    #
    @8
    @0
    @3
    @3
    wa
    @1
    @1
    wa
    w3a
    #
    c.1
    c.1
    cF
    cmulr
    cfv
    #
    co
    cX
    c.x
    co
    c.1
    @4
    c.x
    co
    wceq
    #
    @5
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
    @9
    @4
    cV
    wcel
    c.1
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
    @15
    co
    #
    wceq
    c.1
    c.1
    cF
    cplusg
    cfv
    #
    co
    cX
    c.x
    co
    @16
    wceq
    w3a
    @11
    @5
    @14
    w3a
    @15
    @17
    c.1
    c.1
    c.x
    @10
    c.1
    cF
    @2
    @12
    cV
    cW
    cX
    cX
    @13
    slmdvs1.v
    @15
    eqid
    slmdvs1.s
    @13
    eqid
    slmdvs1.f
    @6
    @17
    eqid
    @10
    eqid
    slmdvs1.u
    @12
    eqid
    slmdlema
    simprd
    simp2d
    syl122anc
end
