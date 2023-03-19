include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "crab.mm"
include "chash.mm"
include "wrex.mm"
include "wn.mm"
include "vtxdusgradjvtx.mm"
include "eqeq1d.mm"
include "c0.mm"
include "cvv.mm"
include "wb.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "wral.mm"
include "rabeq0.mm"
include "wi.mm"
include "ralnex.mm"
include "biimpi.mm"
include "a1i.mm"
include "syl5bi.mm"
include "sylbid.mm"

theorem usgrvd0nedg
  let vv: setvar v
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  assume vtxdusgradjvtx.v: |- V = ( Vtx ` G )
  assume vtxdusgradjvtx.e: |- E = ( Edg ` G )

  disjoint E v
  disjoint G v
  disjoint U v
  disjoint V v
  assert |- ( ( G e. USGraph /\ U e. V ) -> ( ( ( VtxDeg ` G ) ` U ) = 0 -> -. E. v e. V { U , v } e. E ) )

  proof
    cG
    cusgr
    wcel
    cU
    cV
    wcel
    wa
    #
    cU
    cG
    cvtxdg
    cfv
    cfv
    #
    cc0
    wceq
    cU
    vv
    cv
    cpr
    cE
    wcel
    #
    vv
    cV
    crab
    #
    chash
    cfv
    #
    cc0
    wceq
    #
    @2
    vv
    cV
    wrex
    wn
    #
    @0
    @1
    @4
    cc0
    vv
    cU
    cE
    cG
    cV
    vtxdusgradjvtx.v
    vtxdusgradjvtx.e
    vtxdusgradjvtx
    eqeq1d
    @5
    @3
    c0
    wceq
    #
    @0
    @6
    @3
    cvv
    wcel
    @5
    @7
    wb
    @2
    vv
    cV
    cV
    cG
    cvtx
    cfv
    cvv
    vtxdusgradjvtx.v
    cG
    cvtx
    fvex
    eqeltri
    rabex
    @3
    cvv
    hasheq0
    ax-mp
    @7
    @2
    wn
    vv
    cV
    wral
    #
    @0
    @6
    @2
    vv
    cV
    rabeq0
    @8
    @6
    wi
    @0
    @8
    @6
    @2
    vv
    cV
    ralnex
    biimpi
    a1i
    syl5bi
    syl5bi
    sylbid
end
