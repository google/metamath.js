include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "c0.mm"
include "cxnn0.mm"
include "hashxnn0.mm"
include "xnn0ge0.mm"
include "syl.mm"
include "biantrud.mm"
include "cxr.mm"
include "wb.mm"
include "hashxrcl.mm"
include "0xr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "hasheq0.mm"
include "3bitr2d.mm"

theorem hashle00
  let cV: class V
  let cW: class W


  assert |- ( V e. W -> ( ( # ` V ) <_ 0 <-> V = (/) ) )

  proof
    cV
    cW
    wcel
    #
    cV
    chash
    cfv
    #
    cc0
    cle
    wbr
    #
    @2
    cc0
    @1
    cle
    wbr
    #
    wa
    #
    @1
    cc0
    wceq
    #
    cV
    c0
    wceq
    @0
    @3
    @2
    @0
    @1
    cxnn0
    wcel
    @3
    cV
    cW
    hashxnn0
    @1
    xnn0ge0
    syl
    biantrud
    @0
    @1
    cxr
    wcel
    cc0
    cxr
    wcel
    @5
    @4
    wb
    cV
    cW
    hashxrcl
    0xr
    @1
    cc0
    xrletri3
    sylancl
    cV
    cW
    hasheq0
    3bitr2d
end
