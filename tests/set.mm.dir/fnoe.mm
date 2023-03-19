include "con0.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "c1o.mm"
include "cdif.mm"
include "cvv.mm"
include "comu.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "cif.mm"
include "coe.mm"
include "df-oexp.mm"
include "wcel.mm"
include "1on.mm"
include "difexg.mm"
include "ax-mp.mm"
include "fvex.mm"
include "ifex.mm"
include "fnmpt2i.mm"

theorem fnoe
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ^o Fn ( On X. On )

  proof
    vx
    vy
    con0
    con0
    vx
    cv
    #
    c0
    wceq
    #
    c1o
    vy
    cv
    #
    cdif
    #
    @2
    vz
    cvv
    vz
    cv
    @0
    comu
    co
    cmpt
    c1o
    crdg
    #
    cfv
    #
    cif
    coe
    vx
    vy
    vz
    df-oexp
    @1
    @3
    @5
    c1o
    con0
    wcel
    @3
    cvv
    wcel
    1on
    c1o
    @2
    con0
    difexg
    ax-mp
    @2
    @4
    fvex
    ifex
    fnmpt2i
end
