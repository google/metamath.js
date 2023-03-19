include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "cxp.mm"
include "c1st.mm"
include "cbs.mm"
include "cif.mm"
include "wceq.mm"
include "cv.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq12d.mm"
include "df-vtx.mm"
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

theorem vtxval
  let cG: class G
  let vg: setvar g


  assert |- ( Vtx ` G ) = if ( G e. ( _V X. _V ) , ( 1st ` G ) , ( Base ` G ) )

  proof
    cG
    cvv
    wcel
    #
    cG
    cvtx
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
    vg
    cG
    vg
    cv
    #
    @2
    wcel
    #
    @7
    c1st
    cfv
    #
    @7
    cbs
    cfv
    #
    cif
    @6
    cvv
    cvtx
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
    c1st
    fveq2
    @7
    cG
    cbs
    fveq2
    ifbieq12d
    vg
    df-vtx
    @3
    @4
    @5
    cG
    c1st
    fvex
    cG
    cbs
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
    cbs
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
    cvtx
    fvprc
    3eqtr4rd
    pm2.61i
end
