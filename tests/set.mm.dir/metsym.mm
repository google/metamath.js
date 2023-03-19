include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "co.mm"
include "wceq.mm"
include "metxmet.mm"
include "xmetsym.mm"
include "syl3an1.mm"

theorem metsym
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


  assert |- ( ( D e. ( Met ` X ) /\ A e. X /\ B e. X ) -> ( A D B ) = ( B D A ) )

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
    cB
    cA
    cD
    co
    wceq
    cD
    cX
    metxmet
    cA
    cB
    cD
    cX
    xmetsym
    syl3an1
end
