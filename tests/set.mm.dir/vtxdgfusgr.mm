include "cfusgr.mm"
include "wcel.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cn0.mm"
include "vtxdgfusgrf.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"

theorem vtxdgfusgr
  let vv: setvar v
  let cG: class G
  let cV: class V
  assume vtxdgfusgrf.v: |- V = ( Vtx ` G )

  disjoint G v
  assert |- ( G e. FinUSGraph -> A. v e. V ( ( VtxDeg ` G ) ` v ) e. NN0 )

  proof
    cG
    cfusgr
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    cn0
    wcel
    vv
    cV
    @0
    cV
    cn0
    @1
    @2
    cG
    cV
    vtxdgfusgrf.v
    vtxdgfusgrf
    ffvelrnda
    ralrimiva
end
