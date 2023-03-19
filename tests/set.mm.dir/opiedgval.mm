include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "c2nd.mm"
include "cedgf.mm"
include "cif.mm"
include "iedgval.mm"
include "iftrue.mm"
include "syl5eq.mm"

theorem opiedgval
  let cG: class G


  assert |- ( G e. ( _V X. _V ) -> ( iEdg ` G ) = ( 2nd ` G ) )

  proof
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cG
    ciedg
    cfv
    @0
    cG
    c2nd
    cfv
    #
    cG
    cedgf
    cfv
    #
    cif
    @1
    cG
    iedgval
    @0
    @1
    @2
    iftrue
    syl5eq
end
