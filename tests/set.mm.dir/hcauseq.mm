include "ccau.mm"
include "wcel.mm"
include "cn.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "hcau.mm"
include "simplbi.mm"

theorem hcauseq
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let cA: class A


  assert |- ( F e. Cauchy -> F : NN --> ~H )

  proof
    cF
    ccau
    wcel
    cn
    chil
    cF
    wf
    vy
    cv
    #
    cF
    cfv
    vz
    cv
    cF
    cfv
    cmv
    co
    cno
    cfv
    vx
    cv
    clt
    wbr
    vz
    @0
    cuz
    cfv
    wral
    vy
    cn
    wrex
    vx
    crp
    wral
    vx
    vy
    vz
    cF
    hcau
    simplbi
end
