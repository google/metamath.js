include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "ciedg.mm"
include "cop.mm"
include "cvtxdg.mm"
include "cv.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "opex.mm"
include "fvex.mm"
include "opvtxfvi.mm"
include "eqcomi.mm"
include "opiedgfvi.mm"
include "eqid.mm"
include "vtxdgfval.mm"
include "mp1i.mm"
include "df-ov.mm"
include "a1i.mm"
include "3eqtr4rd.mm"

theorem vtxdgop
  let cG: class G
  let cW: class W
  let vu: setvar u
  let vx: setvar x


  assert |- ( G e. W -> ( VtxDeg ` G ) = ( ( Vtx ` G ) VtxDeg ( iEdg ` G ) ) )

  proof
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    #
    cG
    ciedg
    cfv
    #
    cop
    #
    cvtxdg
    cfv
    #
    vu
    @1
    vu
    cv
    #
    vx
    cv
    @2
    cfv
    #
    wcel
    vx
    @2
    cdm
    #
    crab
    chash
    cfv
    @6
    @5
    csn
    wceq
    vx
    @7
    crab
    chash
    cfv
    cxad
    co
    cmpt
    #
    @1
    @2
    cvtxdg
    co
    #
    cG
    cvtxdg
    cfv
    @3
    cvv
    wcel
    @4
    @8
    wceq
    @0
    @1
    @2
    opex
    vx
    vu
    @7
    @3
    @2
    @1
    cvv
    @3
    cvtx
    cfv
    @1
    @2
    @1
    cG
    cvtx
    fvex
    #
    cG
    ciedg
    fvex
    #
    opvtxfvi
    eqcomi
    @3
    ciedg
    cfv
    @2
    @2
    @1
    @10
    @11
    opiedgfvi
    eqcomi
    @7
    eqid
    #
    vtxdgfval
    mp1i
    @9
    @4
    wceq
    @0
    @1
    @2
    cvtxdg
    df-ov
    a1i
    vx
    vu
    @7
    cG
    @2
    @1
    cW
    @1
    eqid
    @2
    eqid
    @12
    vtxdgfval
    3eqtr4rd
end
