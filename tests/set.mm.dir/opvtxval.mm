include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c1st.mm"
include "cbs.mm"
include "cif.mm"
include "vtxval.mm"
include "iftrue.mm"
include "syl5eq.mm"

theorem opvtxval
  let cG: class G


  assert |- ( G e. ( _V X. _V ) -> ( Vtx ` G ) = ( 1st ` G ) )

  proof
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cG
    cvtx
    cfv
    @0
    cG
    c1st
    cfv
    #
    cG
    cbs
    cfv
    #
    cif
    @1
    cG
    vtxval
    @0
    @1
    @2
    iftrue
    syl5eq
end
