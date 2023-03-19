include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "wceq.mm"
include "ssrab2.mm"
include "eqid.mm"
include "mplval.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem mplbas
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vf: setvar f
  let cI: class I
  let c.0: class .0.
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let cX: class X
  assume mplval.p: |- P = ( I mPoly R )
  assume mplval.s: |- S = ( I mPwSer R )
  assume mplval.b: |- B = ( Base ` S )
  assume mplval.z: |- .0. = ( 0g ` R )
  assume mplbas.u: |- U = ( Base ` P )

  disjoint B f
  disjoint I f
  disjoint R f
  disjoint .0. f
  disjoint f i
  disjoint f r
  disjoint f s
  disjoint i r
  disjoint i s
  disjoint I i
  disjoint r s
  disjoint I r
  disjoint I s
  disjoint R i
  disjoint R r
  disjoint R s
  disjoint S i
  disjoint S r
  disjoint S s
  disjoint U i
  disjoint U r
  disjoint U s
  disjoint X f
  assert |- U = { f e. B | f finSupp .0. }

  proof
    cU
    cP
    cbs
    cfv
    #
    vf
    cv
    c.0
    cfsupp
    wbr
    #
    vf
    cB
    crab
    #
    mplbas.u
    @2
    cB
    wss
    @2
    @0
    wceq
    @1
    vf
    cB
    ssrab2
    @2
    cB
    cP
    cS
    cB
    cP
    cR
    cS
    @2
    vf
    cI
    c.0
    mplval.p
    mplval.s
    mplval.b
    mplval.z
    @2
    eqid
    mplval
    mplval.b
    ressbas2
    ax-mp
    eqtr4i
end
