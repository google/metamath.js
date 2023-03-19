include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "ismet2.mm"
include "simplbi.mm"

theorem metxmet
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


  assert |- ( D e. ( Met ` X ) -> D e. ( *Met ` X ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    cD
    cX
    cxmt
    cfv
    wcel
    cX
    cX
    cxp
    cr
    cD
    wf
    cD
    cX
    ismet2
    simplbi
end
