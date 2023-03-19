include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "ccplgr.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wral.mm"
include "rzal.mm"
include "adantl.mm"
include "wb.mm"
include "iscplgr.mm"
include "adantr.mm"
include "mpbird.mm"

theorem cplgr0v
  let cG: class G
  let cV: class V
  let cW: class W
  let vv: setvar v
  assume cplgr0v.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. W /\ V = (/) ) -> G e. ComplGraph )

  proof
    cG
    cW
    wcel
    #
    cV
    c0
    wceq
    #
    wa
    cG
    ccplgr
    wcel
    #
    vv
    cv
    cG
    cuvtx
    cfv
    wcel
    #
    vv
    cV
    wral
    #
    @1
    @4
    @0
    @3
    vv
    cV
    rzal
    adantl
    @0
    @2
    @4
    wb
    @1
    vv
    cG
    cV
    cW
    cplgr0v.v
    iscplgr
    adantr
    mpbird
end
