include "ccusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "wa.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wral.mm"
include "iscusgr.mm"
include "iscplgr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem iscusgrvtx
  let vv: setvar v
  let cG: class G
  let cV: class V
  assume iscusgrvtx.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  assert |- ( G e. ComplUSGraph <-> ( G e. USGraph /\ A. v e. V v e. ( UnivVtx ` G ) ) )

  proof
    cG
    ccusgr
    wcel
    cG
    cusgr
    wcel
    #
    cG
    ccplgr
    wcel
    #
    wa
    @0
    vv
    cv
    cG
    cuvtx
    cfv
    wcel
    vv
    cV
    wral
    #
    wa
    cG
    iscusgr
    @0
    @1
    @2
    vv
    cG
    cV
    cusgr
    iscusgrvtx.v
    iscplgr
    pm5.32i
    bitri
end
