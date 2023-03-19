include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "cplusg.mm"
include "cmulr.mm"
include "wceq.mm"
include "wral.mm"
include "eqid.mm"
include "islfl.mm"
include "simprbda.mm"

theorem lflf
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume lflf.d: |- D = ( Scalar ` W )
  assume lflf.k: |- K = ( Base ` D )
  assume lflf.v: |- V = ( Base ` W )
  assume lflf.f: |- F = ( LFnl ` W )


  assert |- ( ( W e. X /\ G e. F ) -> G : V --> K )

  proof
    cW
    cX
    wcel
    cG
    cF
    wcel
    cV
    cK
    cG
    wf
    vr
    cv
    #
    vx
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    vy
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    cG
    cfv
    @0
    @1
    cG
    cfv
    cD
    cmulr
    cfv
    #
    co
    @3
    cG
    cfv
    cD
    cplusg
    cfv
    #
    co
    wceq
    vy
    cV
    wral
    vx
    cV
    wral
    vr
    cK
    wral
    vx
    vy
    cD
    @4
    @6
    @2
    @5
    cF
    cG
    cK
    cV
    cW
    cX
    vr
    lflf.v
    @4
    eqid
    lflf.d
    @2
    eqid
    lflf.k
    @6
    eqid
    @5
    eqid
    lflf.f
    islfl
    simprbda
end
