include "con0.mm"
include "cv.mm"
include "cvv.mm"
include "csuc.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "coa.mm"
include "df-oadd.mm"
include "fvex.mm"
include "fnmpt2i.mm"

theorem fnoa
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- +o Fn ( On X. On )

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
    csuc
    cmpt
    vx
    cv
    crdg
    #
    cfv
    coa
    vx
    vy
    vz
    df-oadd
    @0
    @1
    fvex
    fnmpt2i
end
