include "cusgr.mm"
include "wcel.mm"
include "cuhgr.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "c0.mm"
include "wi.mm"
include "usgruhgr.mm"
include "uhgrvd00.mm"
include "syl.mm"

theorem usgrvd00
  let vv: setvar v
  let cE: class E
  let cG: class G
  let cV: class V
  let cU: class U
  let ve: setvar e
  assume vtxdusgradjvtx.v: |- V = ( Vtx ` G )
  assume vtxdusgradjvtx.e: |- E = ( Edg ` G )

  disjoint E v
  disjoint G v
  disjoint V v
  disjoint U v
  disjoint E e
  disjoint e v
  disjoint G e
  disjoint V e
  assert |- ( G e. USGraph -> ( A. v e. V ( ( VtxDeg ` G ) ` v ) = 0 -> E = (/) ) )

  proof
    cG
    cusgr
    wcel
    cG
    cuhgr
    wcel
    vv
    cv
    cG
    cvtxdg
    cfv
    cfv
    cc0
    wceq
    vv
    cV
    wral
    cE
    c0
    wceq
    wi
    cG
    usgruhgr
    vv
    cE
    cG
    cV
    vtxdusgradjvtx.v
    vtxdusgradjvtx.e
    uhgrvd00
    syl
end
