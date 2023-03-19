include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "wcel.mm"
include "crgr.mm"
include "wa.mm"
include "cxnn0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "rusgrprop.mm"
include "rgrprop.mm"
include "anim2i.mm"
include "3anass.mm"
include "sylibr.mm"
include "syl.mm"

theorem rusgrprop0
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  assume isrusgr0.v: |- V = ( Vtx ` G )
  assume isrusgr0.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint K v
  assert |- ( G RegUSGraph K -> ( G e. USGraph /\ K e. NN0* /\ A. v e. V ( D ` v ) = K ) )

  proof
    cG
    cK
    crusgr
    wbr
    cG
    cusgr
    wcel
    #
    cG
    cK
    crgr
    wbr
    #
    wa
    #
    @0
    cK
    cxnn0
    wcel
    #
    vv
    cv
    cD
    cfv
    cK
    wceq
    vv
    cV
    wral
    #
    w3a
    #
    cG
    cK
    rusgrprop
    @2
    @0
    @3
    @4
    wa
    #
    wa
    @5
    @1
    @6
    @0
    vv
    cD
    cG
    cK
    cV
    isrusgr0.v
    isrusgr0.d
    rgrprop
    anim2i
    @0
    @3
    @4
    3anass
    sylibr
    syl
end
