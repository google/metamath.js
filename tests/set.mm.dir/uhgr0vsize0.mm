include "cuhgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "uhgr0v0e.mm"
include "ex.mm"
include "cvv.mm"
include "wb.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "cedg.mm"
include "3imtr4g.mm"
include "imp.mm"

theorem uhgr0vsize0
  let cE: class E
  let cG: class G
  let cV: class V
  assume uhgr0v0e.v: |- V = ( Vtx ` G )
  assume uhgr0v0e.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UHGraph /\ ( # ` V ) = 0 ) -> ( # ` E ) = 0 )

  proof
    cG
    cuhgr
    wcel
    #
    cV
    chash
    cfv
    cc0
    wceq
    #
    cE
    chash
    cfv
    cc0
    wceq
    #
    @0
    cV
    c0
    wceq
    #
    cE
    c0
    wceq
    #
    @1
    @2
    @0
    @3
    @4
    cE
    cG
    cV
    uhgr0v0e.v
    uhgr0v0e.e
    uhgr0v0e
    ex
    cV
    cvv
    wcel
    @1
    @3
    wb
    cV
    cG
    cvtx
    cfv
    cvv
    uhgr0v0e.v
    cG
    cvtx
    fvex
    eqeltri
    cV
    cvv
    hasheq0
    ax-mp
    cE
    cvv
    wcel
    @2
    @4
    wb
    cE
    cG
    cedg
    cfv
    cvv
    uhgr0v0e.e
    cG
    cedg
    fvex
    eqeltri
    cE
    cvv
    hasheq0
    ax-mp
    3imtr4g
    imp
end
