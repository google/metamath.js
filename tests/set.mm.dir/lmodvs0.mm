include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "crg.mm"
include "wceq.mm"
include "lmodring.mm"
include "eqid.mm"
include "ringrz.mm"
include "sylan.mm"
include "oveq1d.mm"
include "cbs.mm"
include "simpl.mm"
include "simpr.mm"
include "adantr.mm"
include "ring0cl.mm"
include "syl.mm"
include "lmod0vcl.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "lmod0vs.mm"
include "syldan.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem lmodvs0
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lmodvs0.f: |- F = ( Scalar ` W )
  assume lmodvs0.s: |- .x. = ( .s ` W )
  assume lmodvs0.k: |- K = ( Base ` F )
  assume lmodvs0.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. LMod /\ X e. K ) -> ( X .x. .0. ) = .0. )

  proof
    cW
    clmod
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
    crg
    wcel
    #
    @1
    @5
    @3
    wceq
    cF
    cW
    lmodvs0.f
    lmodring
    #
    cK
    cF
    @4
    cX
    @3
    lmodvs0.k
    @4
    eqid
    #
    @3
    eqid
    #
    ringrz
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
    lmodvs0.k
    @12
    ring0cl
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
    lmodvs0.z
    lmod0vcl
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
    lmodvs0.f
    lmodvs0.s
    lmodvs0.k
    @11
    lmodvsass
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
    lmodvs0.f
    lmodvs0.s
    @12
    lmodvs0.z
    lmod0vs
    syldan
    #
    oveq2d
    eqtrd
    @19
    3eqtr3d
end
