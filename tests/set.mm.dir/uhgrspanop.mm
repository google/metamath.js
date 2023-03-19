include "cuhgr.mm"
include "wcel.mm"
include "cres.mm"
include "cop.mm"
include "cvv.mm"
include "opex.mm"
include "a1i.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ciedg.mm"
include "resex.mm"
include "opvtxfv.mm"
include "mp2an.mm"
include "opiedgfv.mm"
include "id.mm"
include "uhgrspan.mm"

theorem uhgrspanop
  let cA: class A
  let cE: class E
  let cG: class G
  let cV: class V
  assume uhgrspanop.v: |- V = ( Vtx ` G )
  assume uhgrspanop.e: |- E = ( iEdg ` G )


  assert |- ( G e. UHGraph -> <. V , ( E |` A ) >. e. UHGraph )

  proof
    cG
    cuhgr
    wcel
    #
    cA
    cV
    cE
    cA
    cres
    #
    cop
    #
    cE
    cG
    cV
    cvv
    uhgrspanop.v
    uhgrspanop.e
    @2
    cvv
    wcel
    @0
    cV
    @1
    opex
    a1i
    @2
    cvtx
    cfv
    cV
    wceq
    #
    @0
    cV
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    @3
    cV
    cG
    cvtx
    cfv
    cvv
    uhgrspanop.v
    cG
    cvtx
    fvex
    eqeltri
    #
    cE
    cA
    cE
    cG
    ciedg
    cfv
    cvv
    uhgrspanop.e
    cG
    ciedg
    fvex
    eqeltri
    resex
    #
    @1
    cV
    cvv
    cvv
    opvtxfv
    mp2an
    a1i
    @2
    ciedg
    cfv
    @1
    wceq
    #
    @0
    @4
    @5
    @8
    @6
    @7
    @1
    cV
    cvv
    cvv
    opiedgfv
    mp2an
    a1i
    @0
    id
    uhgrspan
end
