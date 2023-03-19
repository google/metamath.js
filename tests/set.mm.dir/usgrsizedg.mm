include "cusgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "chash.mm"
include "crn.mm"
include "cedg.mm"
include "cdm.mm"
include "cvv.mm"
include "cv.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "fvex.mm"
include "dmex.mm"
include "eqid.mm"
include "usgrf.mm"
include "hashf1rn.mm"
include "sylancr.mm"
include "edgval.mm"
include "a1i.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem usgrsizedg
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USGraph -> ( # ` ( iEdg ` G ) ) = ( # ` ( Edg ` G ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cG
    ciedg
    cfv
    #
    chash
    cfv
    #
    @1
    crn
    #
    chash
    cfv
    #
    cG
    cedg
    cfv
    #
    chash
    cfv
    @0
    @1
    cdm
    #
    cvv
    wcel
    @6
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    crab
    #
    @1
    wf1
    @2
    @4
    wceq
    @1
    cG
    ciedg
    fvex
    dmex
    vx
    @1
    cG
    @7
    @7
    eqid
    @1
    eqid
    usgrf
    @6
    @8
    @1
    cvv
    hashf1rn
    sylancr
    @0
    @5
    @3
    chash
    @5
    @3
    wceq
    @0
    cG
    edgval
    a1i
    fveq2d
    eqtr4d
end
