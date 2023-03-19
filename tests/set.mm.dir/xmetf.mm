include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cdm.mm"
include "elfvdm.mm"
include "isxmet.mm"
include "syl.mm"
include "ibi.mm"
include "simpld.mm"

theorem xmetf
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


  assert |- ( D e. ( *Met ` X ) -> D : ( X X. X ) --> RR* )

  proof
    cD
    cX
    cxmt
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
    vy
    cv
    #
    cD
    co
    #
    cc0
    wceq
    @2
    @3
    wceq
    wb
    @4
    vz
    cv
    #
    @2
    cD
    co
    @5
    @3
    cD
    co
    cxad
    co
    cle
    wbr
    vz
    cX
    wral
    wa
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @0
    @1
    @6
    wa
    #
    @0
    cX
    cxmt
    cdm
    #
    wcel
    @0
    @7
    wb
    cD
    cX
    cxmt
    elfvdm
    vx
    vy
    vz
    @8
    cD
    cX
    isxmet
    syl
    ibi
    simpld
end
