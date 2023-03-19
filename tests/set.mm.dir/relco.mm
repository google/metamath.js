include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "ccom.mm"
include "df-co.mm"
include "relopabi.mm"

theorem relco
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- Rel ( A o. B )

  proof
    vx
    cv
    vz
    cv
    #
    cB
    wbr
    @0
    vy
    cv
    cA
    wbr
    wa
    vz
    wex
    vx
    vy
    cA
    cB
    ccom
    vx
    vy
    vz
    cA
    cB
    df-co
    relopabi
end
