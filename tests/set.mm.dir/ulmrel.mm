include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cc.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "w3a.mm"
include "cz.mm"
include "cvv.mm"
include "culm.mm"
include "df-ulm.mm"
include "relmptopab.mm"

theorem ulmrel
  let cS: class S
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Rel ( ~~>u ` S )

  proof
    vn
    cv
    cuz
    cfv
    #
    cc
    vs
    cv
    #
    cmap
    co
    vf
    cv
    #
    wf
    @1
    cc
    vy
    cv
    #
    wf
    vz
    cv
    #
    vk
    cv
    @2
    cfv
    cfv
    @4
    @3
    cfv
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    vz
    @1
    wral
    vk
    vj
    cv
    cuz
    cfv
    wral
    vj
    @0
    wrex
    vx
    crp
    wral
    w3a
    vn
    cz
    wrex
    vs
    vf
    vy
    cvv
    cS
    culm
    vx
    vy
    vz
    vf
    vj
    vk
    vn
    vs
    df-ulm
    relmptopab
end
