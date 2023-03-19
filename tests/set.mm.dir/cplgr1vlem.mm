include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hash1snb.mm"
include "ax-mp.mm"
include "vsnid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "1vgrex.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem cplgr1vlem
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vn: setvar n
  assume cplgr0v.v: |- V = ( Vtx ` G )


  assert |- ( ( # ` V ) = 1 -> G e. _V )

  proof
    cV
    chash
    cfv
    c1
    wceq
    #
    cV
    vn
    cv
    #
    csn
    #
    wceq
    #
    vn
    wex
    #
    cG
    cvv
    wcel
    #
    cV
    cvv
    wcel
    @0
    @4
    wb
    cV
    cG
    cvtx
    cfv
    cvv
    cplgr0v.v
    cG
    cvtx
    fvex
    eqeltri
    cV
    cvv
    vn
    hash1snb
    ax-mp
    @3
    @5
    vn
    @3
    @1
    cV
    wcel
    #
    @5
    @3
    @6
    @1
    @2
    wcel
    vn
    vsnid
    cV
    @2
    @1
    eleq2
    mpbiri
    cG
    @1
    cV
    cplgr0v.v
    1vgrex
    syl
    exlimiv
    sylbi
end
