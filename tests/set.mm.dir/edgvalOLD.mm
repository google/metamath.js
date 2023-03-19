include "wcel.mm"
include "cv.mm"
include "ciedg.mm"
include "cfv.mm"
include "crn.mm"
include "cvv.mm"
include "cedg.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-edg.mm"
include "a1i.mm"
include "fveq2.mm"
include "rneqd.mm"
include "adantl.mm"
include "elex.mm"
include "fvex.mm"
include "rnex.mm"
include "fvmptd.mm"

theorem edgvalOLD
  let cG: class G
  let cV: class V
  let vg: setvar g


  assert |- ( G e. V -> ( Edg ` G ) = ran ( iEdg ` G ) )

  proof
    cG
    cV
    wcel
    #
    vg
    cG
    vg
    cv
    #
    ciedg
    cfv
    #
    crn
    #
    cG
    ciedg
    cfv
    #
    crn
    #
    cvv
    cedg
    cvv
    cedg
    vg
    cvv
    @3
    cmpt
    wceq
    @0
    vg
    df-edg
    a1i
    @1
    cG
    wceq
    #
    @3
    @5
    wceq
    @0
    @6
    @2
    @4
    @1
    cG
    ciedg
    fveq2
    rneqd
    adantl
    cG
    cV
    elex
    @5
    cvv
    wcel
    @0
    @4
    cG
    ciedg
    fvex
    rnex
    a1i
    fvmptd
end
