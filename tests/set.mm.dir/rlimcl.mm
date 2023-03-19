include "crli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "rlimf.mm"
include "rlimss.mm"
include "eqidd.mm"
include "rlim.mm"
include "ibi.mm"
include "simpld.mm"

theorem rlimcl
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k


  assert |- ( F ~~>r A -> A e. CC )

  proof
    cF
    cA
    crli
    wbr
    #
    cA
    cc
    wcel
    #
    vz
    cv
    vx
    cv
    #
    cle
    wbr
    @2
    cF
    cfv
    #
    cA
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    wi
    vx
    cF
    cdm
    #
    wral
    vz
    cr
    wrex
    vy
    crp
    wral
    #
    @0
    @1
    @5
    wa
    @0
    vy
    vz
    vx
    @4
    @3
    cA
    cF
    cA
    cF
    rlimf
    cA
    cF
    rlimss
    @0
    @2
    @4
    wcel
    wa
    @3
    eqidd
    rlim
    ibi
    simpld
end
