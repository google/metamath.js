include "cuhgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "chash.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cedg.mm"
include "cfn.mm"
include "eqid.mm"
include "uhgr0vsize0.mm"
include "c0.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "syl.mm"

theorem uhgr0edgfi
  let cG: class G


  assert |- ( ( G e. UHGraph /\ ( # ` ( Vtx ` G ) ) = 0 ) -> ( Edg ` G ) e. Fin )

  proof
    cG
    cuhgr
    wcel
    cG
    cvtx
    cfv
    #
    chash
    cfv
    cc0
    wceq
    wa
    cG
    cedg
    cfv
    #
    chash
    cfv
    cc0
    wceq
    #
    @1
    cfn
    wcel
    #
    @1
    cG
    @0
    @0
    eqid
    @1
    eqid
    uhgr0vsize0
    @2
    @1
    c0
    wceq
    #
    @3
    @1
    cvv
    wcel
    @2
    @4
    wb
    cG
    cedg
    fvex
    @1
    cvv
    hasheq0
    ax-mp
    @4
    @3
    c0
    cfn
    wcel
    0fin
    @1
    c0
    cfn
    eleq1
    mpbiri
    sylbi
    syl
end
