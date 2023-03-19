include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "co.mm"
include "metf.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem metcl
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


  assert |- ( ( D e. ( Met ` X ) /\ A e. X /\ B e. X ) -> ( A D B ) e. RR )

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
    cr
    wcel
    cD
    cX
    metf
    cA
    cB
    cr
    cX
    cX
    cD
    fovrn
    syl3an1
end
