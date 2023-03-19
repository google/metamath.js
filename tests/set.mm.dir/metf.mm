include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "metflem.mm"
include "simpld.mm"

theorem metf
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


  assert |- ( D e. ( Met ` X ) -> D : ( X X. X ) --> RR )

  proof
    cD
    cX
    cme
    cfv
    wcel
    cX
    cX
    cxp
    cr
    cD
    wf
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
    @0
    @1
    wceq
    wb
    @2
    vz
    cv
    #
    @0
    cD
    co
    @3
    @1
    cD
    co
    caddc
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
    vx
    vy
    vz
    cD
    cX
    metflem
    simpld
end
