include "cho.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "elhmop.mm"
include "simplbi.mm"

theorem hmopf
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. HrmOp -> T : ~H --> ~H )

  proof
    cT
    cho
    wcel
    chil
    chil
    cT
    wf
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    csp
    co
    @0
    cT
    cfv
    @1
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    vx
    vy
    cT
    elhmop
    simplbi
end
