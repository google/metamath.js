include "cslmd.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "csrg.mm"
include "wceq.mm"
include "slmdsrg.mm"
include "eqid.mm"
include "srgrz.mm"
include "sylan.mm"
include "oveq1d.mm"
include "cbs.mm"
include "simpl.mm"
include "simpr.mm"
include "adantr.mm"
include "srg0cl.mm"
include "syl.mm"
include "slmd0vcl.mm"
include "slmdvsass.mm"
include "syl13anc.mm"
include "slmd0vs.mm"
include "syldan.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem slmdvs0
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume slmdvs0.f: |- F = ( Scalar ` W )
  assume slmdvs0.s: |- .x. = ( .s ` W )
  assume slmdvs0.k: |- K = ( Base ` F )
  assume slmdvs0.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. SLMod /\ X e. K ) -> ( X .x. .0. ) = .0. )

  proof
    cW
    cslmd
    wcel
    #
    cX
    cK
    wcel
    #
    wa
    #
    cX
    cF
    c0g
    cfv
    #
    cF
    cmulr
    cfv
    #
    co
    #
    c.0
    c.x
    co
    #
    @3
    c.0
    c.x
    co
    #
    cX
    c.0
    c.x
    co
    #
    c.0
    @2
    @5
    @3
    c.0
    c.x
    @0
    cF
    csrg
    wcel
    #
    @1
    @5
    @3
    wceq
    cF
    cW
    slmdvs0.f
    slmdsrg
    #
    cK
    cF
    @4
    cX
    @3
    slmdvs0.k
    @4
    eqid
    #
    @3
    eqid
    #
    srgrz
    sylan
    oveq1d
    @2
    @6
    cX
    @7
    c.x
    co
    #
    @8
    @2
    @0
    @1
    @3
    cK
    wcel
    #
    c.0
    cW
    cbs
    cfv
    #
    wcel
    #
    @6
    @13
    wceq
    @0
    @1
    simpl
    @0
    @1
    simpr
    @2
    @9
    @14
    @0
    @9
    @1
    @10
    adantr
    cK
    cF
    @3
    slmdvs0.k
    @12
    srg0cl
    syl
    @0
    @16
    @1
    @15
    cW
    c.0
    @15
    eqid
    #
    slmdvs0.z
    slmd0vcl
    adantr
    #
    cX
    @3
    c.x
    @4
    cF
    cK
    @15
    cW
    c.0
    @17
    slmdvs0.f
    slmdvs0.s
    slmdvs0.k
    @11
    slmdvsass
    syl13anc
    @2
    @7
    c.0
    cX
    c.x
    @0
    @1
    @16
    @7
    c.0
    wceq
    @18
    c.x
    cF
    @3
    @15
    cW
    c.0
    c.0
    @17
    slmdvs0.f
    slmdvs0.s
    @12
    slmdvs0.z
    slmd0vs
    syldan
    #
    oveq2d
    eqtrd
    @19
    3eqtr3d
end
