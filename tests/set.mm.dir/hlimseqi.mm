include "chli.mm"
include "wbr.mm"
include "cn.mm"
include "chil.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "hlimi.mm"
include "simplbi.mm"
include "simpld.mm"

theorem hlimseqi
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vf: setvar f
  let cB: class B
  assume hlim.1: |- A e. _V


  assert |- ( F ~~>v A -> F : NN --> ~H )

  proof
    cF
    cA
    chli
    wbr
    #
    cn
    chil
    cF
    wf
    #
    cA
    chil
    wcel
    #
    @0
    @1
    @2
    wa
    vz
    cv
    cF
    cfv
    cA
    cmv
    co
    cno
    cfv
    vx
    cv
    clt
    wbr
    vz
    vy
    cv
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
    cA
    cF
    hlim.1
    hlimi
    simplbi
    simpld
end
