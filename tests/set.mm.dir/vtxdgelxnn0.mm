include "cvv.mm"
include "wcel.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cxnn0.mm"
include "1vgrex.mm"
include "vtxdgf.mm"
include "ffvelrnda.mm"
include "mpancom.mm"

theorem vtxdgelxnn0
  let cG: class G
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  let cW: class W
  assume vtxdgf.v: |- V = ( Vtx ` G )


  assert |- ( X e. V -> ( ( VtxDeg ` G ) ` X ) e. NN0* )

  proof
    cG
    cvv
    wcel
    #
    cX
    cV
    wcel
    cX
    cG
    cvtxdg
    cfv
    #
    cfv
    cxnn0
    wcel
    cG
    cX
    cV
    vtxdgf.v
    1vgrex
    @0
    cV
    cxnn0
    cX
    @1
    cG
    cV
    cvv
    vtxdgf.v
    vtxdgf
    ffvelrnda
    mpancom
end
