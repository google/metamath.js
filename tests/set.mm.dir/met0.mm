include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "metxmet.mm"
include "xmet0.mm"
include "sylan.mm"

theorem met0
  let cA: class A
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C


  assert |- ( ( D e. ( Met ` X ) /\ A e. X ) -> ( A D A ) = 0 )

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
    cA
    cX
    wcel
    cA
    cA
    cD
    co
    cc0
    wceq
    cD
    cX
    metxmet
    cA
    cD
    cX
    xmet0
    sylan
end
