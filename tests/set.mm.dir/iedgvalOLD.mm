include "wcel.mm"
include "cvv.mm"
include "ciedg.mm"
include "cfv.mm"
include "cxp.mm"
include "c2nd.mm"
include "cedgf.mm"
include "cif.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq12d.mm"
include "df-iedg.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem iedgvalOLD
  let cG: class G
  let cV: class V
  let vg: setvar g


  assert |- ( G e. V -> ( iEdg ` G ) = if ( G e. ( _V X. _V ) , ( 2nd ` G ) , ( .ef ` G ) ) )

  proof
    cG
    cV
    wcel
    cG
    cvv
    wcel
    cG
    ciedg
    cfv
    cG
    cvv
    cvv
    cxp
    #
    wcel
    #
    cG
    c2nd
    cfv
    #
    cG
    cedgf
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
    c2nd
    cfv
    #
    @5
    cedgf
    cfv
    #
    cif
    @4
    cvv
    ciedg
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
    c2nd
    fveq2
    @5
    cG
    cedgf
    fveq2
    ifbieq12d
    vg
    df-iedg
    @1
    @2
    @3
    cG
    c2nd
    fvex
    cG
    cedgf
    fvex
    ifex
    fvmpt
    syl
end
