include "cv.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "cshi.mm"
include "cres.mm"
include "subid1.mm"
include "breq1d.mm"
include "pm5.32i.mm"
include "opabbii.mm"
include "wceq.mm"
include "0cn.mm"
include "shftfval.mm"
include "ax-mp.mm"
include "dfres2.mm"
include "3eqtr4i.mm"

theorem shftidt2
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume shftfval.1: |- F e. _V


  assert |- ( F shift 0 ) = ( F |` CC )

  proof
    vx
    cv
    #
    cc
    wcel
    #
    @0
    cc0
    cmin
    co
    #
    vy
    cv
    #
    cF
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    @1
    @0
    @3
    cF
    wbr
    #
    wa
    #
    vx
    vy
    copab
    cF
    cc0
    cshi
    co
    #
    cF
    cc
    cres
    @5
    @8
    vx
    vy
    @1
    @4
    @7
    @1
    @2
    @0
    @3
    cF
    @0
    subid1
    breq1d
    pm5.32i
    opabbii
    cc0
    cc
    wcel
    @9
    @6
    wceq
    0cn
    vx
    vy
    cc0
    cF
    shftfval.1
    shftfval
    ax-mp
    vx
    vy
    cc
    cF
    dfres2
    3eqtr4i
end
