include "cv.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cdvds.mm"
include "df-dvds.mm"
include "relopabi.mm"

theorem reldvds
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Rel ||

  proof
    vx
    cv
    #
    cz
    wcel
    vy
    cv
    #
    cz
    wcel
    wa
    vz
    cv
    @0
    cmul
    co
    @1
    wceq
    vz
    cz
    wrex
    wa
    vx
    vy
    cdvds
    vx
    vy
    vz
    df-dvds
    relopabi
end
