include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "cpw.mm"
include "wa.mm"
include "wn.mm"
include "wal.mm"
include "wo.mm"
include "cgch.mm"
include "enfi.mm"
include "sdomen1.mm"
include "wb.mm"
include "pwen.mm"
include "sdomen2.mm"
include "syl.mm"
include "anbi12d.mm"
include "notbid.mm"
include "albidv.mm"
include "orbi12d.mm"
include "cvv.mm"
include "relen.mm"
include "brrelexi.mm"
include "elgch.mm"
include "brrelex2i.mm"
include "3bitr4d.mm"

theorem engch
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A ~~ B -> ( A e. GCH <-> B e. GCH ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cfn
    wcel
    #
    cA
    vx
    cv
    #
    csdm
    wbr
    #
    @2
    cA
    cpw
    #
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
    cB
    cfn
    wcel
    #
    cB
    @2
    csdm
    wbr
    #
    @2
    cB
    cpw
    #
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
    cA
    cgch
    wcel
    #
    cB
    cgch
    wcel
    #
    @0
    @1
    @10
    @8
    @16
    cA
    cB
    enfi
    @0
    @7
    @15
    vx
    @0
    @6
    @14
    @0
    @3
    @11
    @5
    @13
    cA
    cB
    @2
    sdomen1
    @0
    @4
    @12
    cen
    wbr
    @5
    @13
    wb
    cA
    cB
    pwen
    @4
    @12
    @2
    sdomen2
    syl
    anbi12d
    notbid
    albidv
    orbi12d
    @0
    cA
    cvv
    wcel
    @18
    @9
    wb
    cA
    cB
    cen
    relen
    brrelexi
    vx
    cA
    cvv
    elgch
    syl
    @0
    cB
    cvv
    wcel
    @19
    @17
    wb
    cA
    cB
    cen
    relen
    brrelex2i
    vx
    cB
    cvv
    elgch
    syl
    3bitr4d
end
