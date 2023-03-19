include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "clm0.mm"
include "adantr.mm"
include "oveq1d.mm"
include "clmod.mm"
include "clmlmod.mm"
include "eqid.mm"
include "lmod0vs.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem clm0vs
  let c.x: class .x.
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume clm0vs.v: |- V = ( Base ` W )
  assume clm0vs.f: |- F = ( Scalar ` W )
  assume clm0vs.s: |- .x. = ( .s ` W )
  assume clm0vs.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. CMod /\ X e. V ) -> ( 0 .x. X ) = .0. )

  proof
    cW
    cclm
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cc0
    cX
    c.x
    co
    cF
    c0g
    cfv
    #
    cX
    c.x
    co
    #
    c.0
    @2
    cc0
    @3
    cX
    c.x
    @0
    cc0
    @3
    wceq
    @1
    cF
    cW
    clm0vs.f
    clm0
    adantr
    oveq1d
    @0
    cW
    clmod
    wcel
    @1
    @4
    c.0
    wceq
    cW
    clmlmod
    c.x
    cF
    @3
    cV
    cW
    cX
    c.0
    clm0vs.v
    clm0vs.f
    clm0vs.s
    @3
    eqid
    clm0vs.z
    lmod0vs
    sylan
    eqtrd
end
