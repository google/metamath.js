include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "co.mm"
include "xmetf.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem xmetcl
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


  assert |- ( ( D e. ( *Met ` X ) /\ A e. X /\ B e. X ) -> ( A D B ) e. RR* )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cX
    cX
    cxp
    cxr
    cD
    wf
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
    cxr
    wcel
    cD
    cX
    xmetf
    cA
    cB
    cxr
    cX
    cX
    cD
    fovrn
    syl3an1
end
