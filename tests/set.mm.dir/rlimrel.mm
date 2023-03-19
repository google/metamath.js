include "cv.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "crli.mm"
include "df-rlim.mm"
include "relopabi.mm"

theorem rlimrel
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vm: setvar m


  assert |- Rel ~~>r

  proof
    vf
    cv
    #
    cc
    cr
    cpm
    co
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
    @2
    @0
    cfv
    @1
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
    @0
    cdm
    wral
    vz
    cr
    wrex
    vy
    crp
    wral
    wa
    vf
    vx
    crli
    vx
    vy
    vz
    vw
    vf
    df-rlim
    relopabi
end
