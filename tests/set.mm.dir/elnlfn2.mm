include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cnl.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "elnlfn.mm"
include "simplbda.mm"

theorem elnlfn2
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T : ~H --> CC /\ A e. ( null ` T ) ) -> ( T ` A ) = 0 )

  proof
    chil
    cc
    cT
    wf
    cA
    cT
    cnl
    cfv
    wcel
    cA
    chil
    wcel
    cA
    cT
    cfv
    cc0
    wceq
    cA
    cT
    elnlfn
    simplbda
end
