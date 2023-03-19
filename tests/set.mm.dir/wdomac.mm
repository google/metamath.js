include "cwdom.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cdom.mm"
include "relwdom.mm"
include "brrelex2i.mm"
include "reldom.mm"
include "ccrd.mm"
include "cdm.mm"
include "wb.mm"
include "numth3.mm"
include "wdomnumr.mm"
include "syl.mm"
include "pm5.21nii.mm"

theorem wdomac
  let cX: class X
  let cY: class Y


  assert |- ( X ~<_* Y <-> X ~<_ Y )

  proof
    cX
    cY
    cwdom
    wbr
    #
    cY
    cvv
    wcel
    #
    cX
    cY
    cdom
    wbr
    #
    cX
    cY
    cwdom
    relwdom
    brrelex2i
    cX
    cY
    cdom
    reldom
    brrelex2i
    @1
    cY
    ccrd
    cdm
    wcel
    @0
    @2
    wb
    cY
    cvv
    numth3
    cX
    cY
    wdomnumr
    syl
    pm5.21nii
end
