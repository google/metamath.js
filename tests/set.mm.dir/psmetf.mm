include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "ispsmet.mm"
include "syl.mm"
include "ibi.mm"
include "simpld.mm"

theorem psmetf
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( D e. ( PsMet ` X ) -> D : ( X X. X ) --> RR* )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cX
    cX
    cxp
    cxr
    cD
    wf
    #
    va
    cv
    #
    @2
    cD
    co
    cc0
    wceq
    @2
    vb
    cv
    #
    cD
    co
    vc
    cv
    #
    @2
    cD
    co
    @4
    @3
    cD
    co
    cxad
    co
    cle
    wbr
    vc
    cX
    wral
    vb
    cX
    wral
    wa
    va
    cX
    wral
    #
    @0
    @1
    @5
    wa
    #
    @0
    cX
    cvv
    wcel
    @0
    @6
    wb
    cD
    cX
    cpsmet
    elfvex
    va
    vb
    vc
    cD
    cvv
    cX
    ispsmet
    syl
    ibi
    simpld
end
