include "wcel.mm"
include "wa.mm"
include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "crgr.mm"
include "cxnn0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "isrusgr.mm"
include "isrgr.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem isrusgr0
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume isrusgr0.v: |- V = ( Vtx ` G )
  assume isrusgr0.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint K v
  assert |- ( ( G e. W /\ K e. Z ) -> ( G RegUSGraph K <-> ( G e. USGraph /\ K e. NN0* /\ A. v e. V ( D ` v ) = K ) ) )

  proof
    cG
    cW
    wcel
    cK
    cZ
    wcel
    wa
    #
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
    @1
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
    cW
    cZ
    isrusgr
    @0
    @3
    @1
    @4
    @5
    wa
    #
    wa
    @6
    @0
    @2
    @7
    @1
    vv
    cD
    cG
    cK
    cV
    cW
    cZ
    isrusgr0.v
    isrusgr0.d
    isrgr
    anbi2d
    @1
    @4
    @5
    3anass
    syl6bbr
    bitrd
end
