include "cusgr.mm"
include "wcel.mm"
include "cxnn0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "crusgr.mm"
include "wbr.mm"
include "wb.mm"
include "isrusgr0.mm"
include "3adant3.mm"
include "ibir.mm"

theorem usgreqdrusgr
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  assume isrusgr0.v: |- V = ( Vtx ` G )
  assume isrusgr0.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint K v
  assert |- ( ( G e. USGraph /\ K e. NN0* /\ A. v e. V ( D ` v ) = K ) -> G RegUSGraph K )

  proof
    cG
    cusgr
    wcel
    #
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
    crusgr
    wbr
    #
    @0
    @1
    @4
    @3
    wb
    @2
    vv
    cD
    cG
    cK
    cV
    cusgr
    cxnn0
    isrusgr0.v
    isrusgr0.d
    isrusgr0
    3adant3
    ibir
end
