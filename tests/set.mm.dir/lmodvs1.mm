include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "eqid.mm"
include "lmod1cl.mm"
include "adantr.mm"
include "simpr.mm"
include "w3a.mm"
include "cplusg.mm"
include "cmulr.mm"
include "lmodlema.mm"
include "simprrd.mm"
include "syl122anc.mm"

theorem lmodvs1
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  assume lmodvs1.v: |- V = ( Base ` W )
  assume lmodvs1.f: |- F = ( Scalar ` W )
  assume lmodvs1.s: |- .x. = ( .s ` W )
  assume lmodvs1.u: |- .1. = ( 1r ` F )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( .1. .x. X ) = X )

  proof
    cW
    clmod
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
    lmodvs1.f
    @2
    eqid
    #
    lmodvs1.u
    lmod1cl
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
    @9
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
    @10
    wceq
    w3a
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
    @5
    @9
    @11
    c.1
    c.1
    c.x
    @12
    c.1
    cF
    @2
    cV
    cW
    cX
    cX
    lmodvs1.v
    @9
    eqid
    lmodvs1.s
    lmodvs1.f
    @6
    @11
    eqid
    @12
    eqid
    lmodvs1.u
    lmodlema
    simprrd
    syl122anc
end
