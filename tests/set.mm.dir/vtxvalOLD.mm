include "wcel.mm"
include "cvv.mm"
include "cvtx.mm"
include "cfv.mm"
include "cxp.mm"
include "c1st.mm"
include "cbs.mm"
include "cif.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq12d.mm"
include "df-vtx.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem vtxvalOLD
  let cG: class G
  let cV: class V
  let vg: setvar g


  assert |- ( G e. V -> ( Vtx ` G ) = if ( G e. ( _V X. _V ) , ( 1st ` G ) , ( Base ` G ) ) )

  proof
    cG
    cV
    wcel
    cG
    cvv
    wcel
    cG
    cvtx
    cfv
    cG
    cvv
    cvv
    cxp
    #
    wcel
    #
    cG
    c1st
    cfv
    #
    cG
    cbs
    cfv
    #
    cif
    #
    wceq
    cG
    cV
    elex
    vg
    cG
    vg
    cv
    #
    @0
    wcel
    #
    @5
    c1st
    cfv
    #
    @5
    cbs
    cfv
    #
    cif
    @4
    cvv
    cvtx
    @5
    cG
    wceq
    @6
    @1
    @7
    @8
    @2
    @3
    @5
    cG
    @0
    eleq1
    @5
    cG
    c1st
    fveq2
    @5
    cG
    cbs
    fveq2
    ifbieq12d
    vg
    df-vtx
    @1
    @2
    @3
    cG
    c1st
    fvex
    cG
    cbs
    fvex
    ifex
    fvmpt
    syl
end
