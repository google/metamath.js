include "clo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "ellnop.mm"
include "simplbi.mm"

theorem lnopf
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. LinOp -> T : ~H --> ~H )

  proof
    cT
    clo
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
    csm
    co
    vz
    cv
    #
    cva
    co
    cT
    cfv
    @0
    @1
    cT
    cfv
    csm
    co
    @2
    cT
    cfv
    cva
    co
    wceq
    vz
    chil
    wral
    vy
    chil
    wral
    vx
    cc
    wral
    vx
    vy
    vz
    cT
    ellnop
    simplbi
end
