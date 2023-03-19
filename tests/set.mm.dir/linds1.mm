include "clinds.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "islinds.mm"
include "syl.mm"
include "ibi.mm"
include "simpld.mm"

theorem linds1
  let cB: class B
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vw: setvar w
  assume islinds.b: |- B = ( Base ` W )


  assert |- ( X e. ( LIndS ` W ) -> X C_ B )

  proof
    cX
    cW
    clinds
    cfv
    wcel
    #
    cX
    cB
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
    @1
    @2
    wa
    #
    @0
    cW
    clinds
    cdm
    #
    wcel
    @0
    @3
    wb
    cX
    cW
    clinds
    elfvdm
    cB
    @4
    cW
    cX
    islinds.b
    islinds
    syl
    ibi
    simpld
end
