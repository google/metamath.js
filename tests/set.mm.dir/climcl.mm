include "cli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "cvv.mm"
include "climrel.mm"
include "brrelexi.mm"
include "eqidd.mm"
include "clim.mm"
include "ibi.mm"
include "simpld.mm"

theorem climcl
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k


  assert |- ( F ~~> A -> A e. CC )

  proof
    cF
    cA
    cli
    wbr
    #
    cA
    cc
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    @3
    cA
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    wa
    vk
    vj
    cv
    cuz
    cfv
    wral
    vj
    cz
    wrex
    vx
    crp
    wral
    #
    @0
    @1
    @4
    wa
    @0
    vx
    cA
    @3
    vj
    vk
    cF
    cvv
    cF
    cA
    cli
    climrel
    brrelexi
    @0
    @2
    cz
    wcel
    wa
    @3
    eqidd
    clim
    ibi
    simpld
end
