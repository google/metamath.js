include "cfusgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "cfn.mm"
include "w3a.mm"
include "c2.mm"
include "cv.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "chash.mm"
include "fusgrfupgrfs.mm"
include "vtxdgoddnumeven.mm"
include "syl.mm"

theorem fusgrvtxdgonume
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cI: class I
  let cV: class V
  let vw: setvar w
  assume finsumvtxdgeven.v: |- V = ( Vtx ` G )
  assume finsumvtxdgeven.i: |- I = ( iEdg ` G )
  assume finsumvtxdgeven.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint V v
  disjoint D v
  disjoint I v
  disjoint D w
  disjoint v w
  disjoint G w
  disjoint I w
  disjoint V w
  assert |- ( G e. FinUSGraph -> 2 || ( # ` { v e. V | -. 2 || ( D ` v ) } ) )

  proof
    cG
    cfusgr
    wcel
    cG
    cupgr
    wcel
    cV
    cfn
    wcel
    cI
    cfn
    wcel
    w3a
    c2
    c2
    vv
    cv
    cD
    cfv
    cdvds
    wbr
    wn
    vv
    cV
    crab
    chash
    cfv
    cdvds
    wbr
    cG
    cI
    cV
    finsumvtxdgeven.v
    finsumvtxdgeven.i
    fusgrfupgrfs
    vv
    cD
    cG
    cI
    cV
    finsumvtxdgeven.v
    finsumvtxdgeven.i
    finsumvtxdgeven.d
    vtxdgoddnumeven
    syl
end
