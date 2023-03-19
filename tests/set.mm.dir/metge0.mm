include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "cc0.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "metxmet.mm"
include "xmetge0.mm"
include "syl3an1.mm"

theorem metge0
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


  assert |- ( ( D e. ( Met ` X ) /\ A e. X /\ B e. X ) -> 0 <_ ( A D B ) )

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
    cc0
    cA
    cB
    cD
    co
    cle
    wbr
    cD
    cX
    metxmet
    cA
    cB
    cD
    cX
    xmetge0
    syl3an1
end
