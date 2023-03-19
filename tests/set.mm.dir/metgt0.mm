include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "wne.mm"
include "cc0.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "metxmet.mm"
include "xmetgt0.mm"
include "syl3an1.mm"

theorem metgt0
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


  assert |- ( ( D e. ( Met ` X ) /\ A e. X /\ B e. X ) -> ( A =/= B <-> 0 < ( A D B ) ) )

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
    wne
    cc0
    cA
    cB
    cD
    co
    clt
    wbr
    wb
    cD
    cX
    metxmet
    cA
    cB
    cD
    cX
    xmetgt0
    syl3an1
end
