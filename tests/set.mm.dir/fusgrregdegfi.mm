include "cfusgr.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cn0.mm"
include "wi.mm"
include "cvtxdg.mm"
include "vtxdgfusgr.mm"
include "wa.mm"
include "r19.26.mm"
include "wb.mm"
include "fveq1i.mm"
include "eqeq1i.mm"
include "eleq1.mm"
include "sylbi.mm"
include "biimpac.mm"
include "ralimi.mm"
include "rspn0.mm"
include "syl5com.mm"
include "sylbir.mm"
include "ex.mm"
include "com23.mm"
include "syl.mm"
include "imp.mm"

theorem fusgrregdegfi
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
  assert |- ( ( G e. FinUSGraph /\ V =/= (/) ) -> ( A. v e. V ( D ` v ) = K -> K e. NN0 ) )

  proof
    cG
    cfusgr
    wcel
    #
    cV
    c0
    wne
    #
    vv
    cv
    #
    cD
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    cK
    cn0
    wcel
    #
    wi
    #
    @0
    @2
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cn0
    wcel
    #
    vv
    cV
    wral
    #
    @1
    @7
    wi
    vv
    cG
    cV
    isrusgr0.v
    vtxdgfusgr
    @11
    @5
    @1
    @6
    @11
    @5
    @1
    @6
    wi
    #
    @11
    @5
    wa
    @10
    @4
    wa
    #
    vv
    cV
    wral
    #
    @12
    @10
    @4
    vv
    cV
    r19.26
    @14
    @6
    vv
    cV
    wral
    @1
    @6
    @13
    @6
    vv
    cV
    @4
    @10
    @6
    @4
    @9
    cK
    wceq
    @10
    @6
    wb
    @3
    @9
    cK
    @2
    cD
    @8
    isrusgr0.d
    fveq1i
    eqeq1i
    @9
    cK
    cn0
    eleq1
    sylbi
    biimpac
    ralimi
    @6
    vv
    cV
    rspn0
    syl5com
    sylbir
    ex
    com23
    syl
    imp
end
