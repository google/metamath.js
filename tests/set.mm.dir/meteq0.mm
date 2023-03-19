include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "metxmet.mm"
include "xmeteq0.mm"
include "syl3an1.mm"

theorem meteq0
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C


  assert |- ( ( D e. ( Met ` X ) /\ A e. X /\ B e. X ) -> ( ( A D B ) = 0 <-> A = B ) )

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
    cB
    cX
    wcel
    cA
    cB
    cD
    co
    cc0
    wceq
    cA
    cB
    wceq
    wb
    cD
    cX
    metxmet
    cA
    cB
    cD
    cX
    xmeteq0
    syl3an1
end
