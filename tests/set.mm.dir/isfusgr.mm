include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "cusgr.mm"
include "cfusgr.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "df-fusgr.mm"
include "elrab2.mm"

theorem isfusgr
  let cG: class G
  let cV: class V
  let vg: setvar g
  assume isfusgr.v: |- V = ( Vtx ` G )


  assert |- ( G e. FinUSGraph <-> ( G e. USGraph /\ V e. Fin ) )

  proof
    vg
    cv
    #
    cvtx
    cfv
    #
    cfn
    wcel
    cV
    cfn
    wcel
    vg
    cG
    cusgr
    cfusgr
    @0
    cG
    wceq
    #
    @1
    cV
    cfn
    @2
    @1
    cG
    cvtx
    cfv
    cV
    @0
    cG
    cvtx
    fveq2
    isfusgr.v
    syl6eqr
    eleq1d
    vg
    df-fusgr
    elrab2
end
