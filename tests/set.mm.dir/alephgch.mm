include "csuc.mm"
include "cale.mm"
include "cfv.mm"
include "cpw.mm"
include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "wa.mm"
include "wn.mm"
include "wal.mm"
include "wo.mm"
include "cgch.mm"
include "alephnbtwn2.mm"
include "sdomen2.mm"
include "anbi2d.mm"
include "mtbii.mm"
include "alrimiv.mm"
include "olcd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "elgch.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem alephgch
  let cA: class A
  let vx: setvar x


  assert |- ( ( aleph ` suc A ) ~~ ~P ( aleph ` A ) -> ( aleph ` A ) e. GCH )

  proof
    cA
    csuc
    cale
    cfv
    #
    cA
    cale
    cfv
    #
    cpw
    #
    cen
    wbr
    #
    @1
    cfn
    wcel
    #
    @1
    vx
    cv
    #
    csdm
    wbr
    #
    @5
    @2
    csdm
    wbr
    #
    wa
    #
    wn
    #
    vx
    wal
    #
    wo
    #
    @1
    cgch
    wcel
    #
    @3
    @10
    @4
    @3
    @9
    vx
    @3
    @6
    @5
    @0
    csdm
    wbr
    #
    wa
    @8
    cA
    @5
    alephnbtwn2
    @3
    @13
    @7
    @6
    @0
    @2
    @5
    sdomen2
    anbi2d
    mtbii
    alrimiv
    olcd
    @1
    cvv
    wcel
    @12
    @11
    wb
    cA
    cale
    fvex
    vx
    @1
    cvv
    elgch
    ax-mp
    sylibr
end
