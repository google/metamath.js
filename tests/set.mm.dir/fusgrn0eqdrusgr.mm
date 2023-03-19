include "cfusgr.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "fusgrusgr.mm"
include "ad2antrr.mm"
include "cn0.mm"
include "fusgrregdegfi.mm"
include "imp.mm"
include "nn0xnn0d.mm"
include "simpr.mm"
include "usgreqdrusgr.mm"
include "syl3anc.mm"
include "ex.mm"

theorem fusgrn0eqdrusgr
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  assume isrusgr0.v: |- V = ( Vtx ` G )
  assume isrusgr0.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint K v
  disjoint V v
  assert |- ( ( G e. FinUSGraph /\ V =/= (/) ) -> ( A. v e. V ( D ` v ) = K -> G RegUSGraph K ) )

  proof
    cG
    cfusgr
    wcel
    #
    cV
    c0
    wne
    #
    wa
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
    cG
    cK
    crusgr
    wbr
    #
    @2
    @3
    wa
    #
    cG
    cusgr
    wcel
    #
    cK
    cxnn0
    wcel
    @3
    @4
    @0
    @6
    @1
    @3
    cG
    fusgrusgr
    ad2antrr
    @5
    cK
    @2
    @3
    cK
    cn0
    wcel
    vv
    cD
    cG
    cK
    cV
    isrusgr0.v
    isrusgr0.d
    fusgrregdegfi
    imp
    nn0xnn0d
    @2
    @3
    simpr
    vv
    cD
    cG
    cK
    cV
    isrusgr0.v
    isrusgr0.d
    usgreqdrusgr
    syl3anc
    ex
end
