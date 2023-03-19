include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cpsmet.mm"
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
include "xmetf.mm"
include "xmet0.mm"
include "w3a.mm"
include "3anrot.mm"
include "xmettri2.mm"
include "sylan2br.mm"
include "3anassrs.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "ispsmet.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem xmetpsmet
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C


  assert |- ( D e. ( *Met ` X ) -> D e. ( PsMet ` X ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
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
    vx
    cv
    #
    @3
    cD
    co
    cc0
    wceq
    #
    @3
    vy
    cv
    #
    cD
    co
    vz
    cv
    #
    @3
    cD
    co
    @6
    @5
    cD
    co
    cxad
    co
    cle
    wbr
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    #
    wa
    #
    vx
    cX
    wral
    #
    cD
    cX
    xmetf
    @0
    @10
    vx
    cX
    @0
    @3
    cX
    wcel
    #
    wa
    #
    @4
    @9
    @3
    cD
    cX
    xmet0
    @13
    @8
    vy
    cX
    @13
    @5
    cX
    wcel
    #
    wa
    @7
    vz
    cX
    @0
    @12
    @14
    @6
    cX
    wcel
    #
    @7
    @12
    @14
    @15
    w3a
    @0
    @15
    @12
    @14
    w3a
    @7
    @15
    @12
    @14
    3anrot
    @3
    @5
    @6
    cD
    cX
    xmettri2
    sylan2br
    3anassrs
    ralrimiva
    ralrimiva
    jca
    ralrimiva
    @0
    cX
    cvv
    wcel
    @1
    @2
    @11
    wa
    wb
    cD
    cX
    cxmt
    elfvex
    vx
    vy
    vz
    cD
    cvv
    cX
    ispsmet
    syl
    mpbir2and
end
