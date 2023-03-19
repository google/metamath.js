include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cplusg.mm"
include "cbs.mm"
include "wceq.mm"
include "simpll.mm"
include "simprl.mm"
include "eqid.mm"
include "lssel.mm"
include "ad2ant2l.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmod0vrid.mm"
include "syl2anc.mm"
include "simplr.mm"
include "simprr.mm"
include "lss0cl.mm"
include "adantr.mm"
include "lsscl.mm"
include "syl13anc.mm"
include "eqeltrrd.mm"

theorem lssvscl
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lssvscl.f: |- F = ( Scalar ` W )
  assume lssvscl.t: |- .x. = ( .s ` W )
  assume lssvscl.b: |- B = ( Base ` F )
  assume lssvscl.s: |- S = ( LSubSp ` W )


  assert |- ( ( ( W e. LMod /\ U e. S ) /\ ( X e. B /\ Y e. U ) ) -> ( X .x. Y ) e. U )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cU
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    c.x
    co
    #
    cW
    c0g
    cfv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    @7
    cU
    @6
    @0
    @7
    cW
    cbs
    cfv
    #
    wcel
    #
    @10
    @7
    wceq
    @0
    @1
    @5
    simpll
    #
    @6
    @0
    @3
    cY
    @11
    wcel
    #
    @12
    @13
    @2
    @3
    @4
    simprl
    #
    @1
    @4
    @14
    @0
    @3
    cS
    cU
    @11
    cW
    cY
    @11
    eqid
    #
    lssvscl.s
    lssel
    ad2ant2l
    cX
    c.x
    cF
    cB
    @11
    cW
    cY
    @16
    lssvscl.f
    lssvscl.t
    lssvscl.b
    lmodvscl
    syl3anc
    @9
    @11
    cW
    @7
    @8
    @16
    @9
    eqid
    #
    @8
    eqid
    #
    lmod0vrid
    syl2anc
    @6
    @1
    @3
    @4
    @8
    cU
    wcel
    #
    @10
    cU
    wcel
    @0
    @1
    @5
    simplr
    @15
    @2
    @3
    @4
    simprr
    @2
    @19
    @5
    cS
    cU
    cW
    @8
    @18
    lssvscl.s
    lss0cl
    adantr
    cB
    @9
    cS
    c.x
    cU
    cF
    cW
    cY
    @8
    cX
    lssvscl.f
    lssvscl.b
    @17
    lssvscl.t
    lssvscl.s
    lsscl
    syl13anc
    eqeltrrd
end
