include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "cdm.mm"
include "wceq.mm"
include "metxmet.mm"
include "xmetdmdm.mm"
include "syl.mm"

theorem metdmdm
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


  assert |- ( D e. ( Met ` X ) -> X = dom dom D )

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
    cD
    cdm
    cdm
    wceq
    cD
    cX
    metxmet
    cD
    cX
    xmetdmdm
    syl
end
