include "con0.mm"
include "cv.mm"
include "cvv.mm"
include "coa.mm"
include "co.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "comu.mm"
include "df-omul.mm"
include "fvex.mm"
include "fnmpt2i.mm"

theorem fnom
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- .o Fn ( On X. On )

  proof
    vx
    vy
    con0
    con0
    vy
    cv
    #
    vz
    cvv
    vz
    cv
    vx
    cv
    coa
    co
    cmpt
    c0
    crdg
    #
    cfv
    comu
    vx
    vy
    vz
    df-omul
    @0
    @1
    fvex
    fnmpt2i
end
