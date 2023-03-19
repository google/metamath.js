include "cvv.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cxp.mm"
include "c2nd.mm"
include "cedgf.mm"
include "cif.mm"
include "wceq.mm"
include "cv.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq12d.mm"
include "df-iedg.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "prcnel.mm"
include "iffalsed.mm"
include "3eqtr4rd.mm"
include "pm2.61i.mm"

theorem iedgval
  let cG: class G
  let vg: setvar g


  assert |- ( iEdg ` G ) = if ( G e. ( _V X. _V ) , ( 2nd ` G ) , ( .ef ` G ) )

  proof
    cG
    cvv
    wcel
    #
    cG
    ciedg
    cfv
    #
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
    vg
    cG
    vg
    cv
    #
    @2
    wcel
    #
    @7
    c2nd
    cfv
    #
    @7
    cedgf
    cfv
    #
    cif
    @6
    cvv
    ciedg
    @7
    cG
    wceq
    @8
    @3
    @9
    @10
    @4
    @5
    @7
    cG
    @2
    eleq1
    @7
    cG
    c2nd
    fveq2
    @7
    cG
    cedgf
    fveq2
    ifbieq12d
    vg
    df-iedg
    @3
    @4
    @5
    cG
    c2nd
    fvex
    cG
    cedgf
    fvex
    ifex
    fvmpt
    @0
    wn
    #
    @5
    c0
    @6
    @1
    cG
    cedgf
    fvprc
    @11
    @3
    @4
    @5
    cG
    @2
    prcnel
    iffalsed
    cG
    ciedg
    fvprc
    3eqtr4rd
    pm2.61i
end
