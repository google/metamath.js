include "clf.mm"
include "wcel.mm"
include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wral.mm"
include "ellnfn.mm"
include "simplbi.mm"

theorem lnfnf
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. LinFn -> T : ~H --> CC )

  proof
    cT
    clf
    wcel
    chil
    cc
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
    cmul
    co
    @2
    cT
    cfv
    caddc
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
    ellnfn
    simplbi
end
