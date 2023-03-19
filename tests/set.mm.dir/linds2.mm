include "clinds.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "eqid.mm"
include "islinds.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"

theorem linds2
  let cW: class W
  let cX: class X


  assert |- ( X e. ( LIndS ` W ) -> ( _I |` X ) LIndF W )

  proof
    cX
    cW
    clinds
    cfv
    wcel
    #
    cX
    cW
    cbs
    cfv
    #
    wss
    #
    cid
    cX
    cres
    cW
    clindf
    wbr
    #
    @0
    @2
    @3
    wa
    #
    @0
    cW
    clinds
    cdm
    #
    wcel
    @0
    @4
    wb
    cX
    cW
    clinds
    elfvdm
    @1
    @5
    cW
    cX
    @1
    eqid
    islinds
    syl
    ibi
    simprd
end
