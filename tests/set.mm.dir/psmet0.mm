include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "ispsmet.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "simpld.mm"
include "ralrimiva.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "mpan9.mm"

theorem psmet0
  let cA: class A
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( D e. ( PsMet ` X ) /\ A e. X ) -> ( A D A ) = 0 )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    va
    cv
    #
    @1
    cD
    co
    #
    cc0
    wceq
    #
    va
    cX
    wral
    cA
    cX
    wcel
    cA
    cA
    cD
    co
    #
    cc0
    wceq
    #
    @0
    @3
    va
    cX
    @0
    @1
    cX
    wcel
    wa
    @3
    @1
    vb
    cv
    #
    cD
    co
    vc
    cv
    #
    @1
    cD
    co
    @7
    @6
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
    #
    @0
    @3
    @8
    wa
    #
    va
    cX
    @0
    cX
    cX
    cxp
    cxr
    cD
    wf
    #
    @9
    va
    cX
    wral
    #
    @0
    @10
    @11
    wa
    #
    @0
    cX
    cvv
    wcel
    @0
    @12
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
    simprd
    r19.21bi
    simpld
    ralrimiva
    @3
    @5
    va
    cA
    cX
    @1
    cA
    wceq
    #
    @2
    @4
    cc0
    @13
    @1
    cA
    @1
    cA
    cD
    @13
    id
    #
    @14
    oveq12d
    eqeq1d
    rspcv
    mpan9
end
