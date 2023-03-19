include "cv.mm"
include "cc.mm"
include "wcel.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "cli.mm"
include "df-clim.mm"
include "relopabi.mm"

theorem climrel
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vm: setvar m


  assert |- Rel ~~>

  proof
    vy
    cv
    #
    cc
    wcel
    vk
    cv
    vf
    cv
    cfv
    #
    cc
    wcel
    @1
    @0
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
    wa
    vf
    vy
    cli
    vx
    vy
    vf
    vj
    vk
    df-clim
    relopabi
end
