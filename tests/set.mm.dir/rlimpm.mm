include "crli.mm"
include "wbr.mm"
include "cdm.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "copab.mm"
include "df-rlim.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "dmss.mm"
include "ax-mp.mm"
include "dmxpss.mm"
include "sstri.mm"
include "rlimrel.mm"
include "releldmi.mm"
include "sseldi.mm"

theorem rlimpm
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k


  assert |- ( F ~~>r A -> F e. ( CC ^pm RR ) )

  proof
    cF
    cA
    crli
    wbr
    crli
    cdm
    #
    cc
    cr
    cpm
    co
    #
    cF
    @0
    @1
    cc
    cxp
    #
    cdm
    #
    @1
    crli
    @2
    wss
    @0
    @3
    wss
    crli
    vf
    cv
    #
    @1
    wcel
    vx
    cv
    #
    cc
    wcel
    wa
    vz
    cv
    vw
    cv
    #
    cle
    wbr
    @6
    @4
    cfv
    @5
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    wi
    vw
    @4
    cdm
    wral
    vz
    cr
    wrex
    vy
    crp
    wral
    #
    wa
    vf
    vx
    copab
    @2
    vx
    vy
    vz
    vw
    vf
    df-rlim
    @7
    vf
    vx
    @1
    cc
    opabssxp
    eqsstri
    crli
    @2
    dmss
    ax-mp
    @1
    cc
    dmxpss
    sstri
    cF
    cA
    crli
    rlimrel
    releldmi
    sseldi
end
