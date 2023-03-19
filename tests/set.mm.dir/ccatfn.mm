include "cvv.mm"
include "cc0.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wcel.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cconcat.mm"
include "df-concat.mm"
include "ovex.mm"
include "mptex.mm"
include "fnmpt2i.mm"

theorem ccatfn
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x


  assert |- ++ Fn ( _V X. _V )

  proof
    vs
    vt
    cvv
    cvv
    vx
    cc0
    vs
    cv
    #
    chash
    cfv
    #
    vt
    cv
    #
    chash
    cfv
    caddc
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    @1
    cfzo
    co
    wcel
    @5
    @0
    cfv
    @5
    @1
    cmin
    co
    @2
    cfv
    cif
    #
    cmpt
    cconcat
    vx
    vt
    vs
    df-concat
    vx
    @4
    @6
    cc0
    @3
    cfzo
    ovex
    mptex
    fnmpt2i
end
