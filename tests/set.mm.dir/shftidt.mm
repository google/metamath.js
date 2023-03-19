include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cshi.mm"
include "co.mm"
include "cfv.mm"
include "cres.mm"
include "shftidt2.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eq.mm"

theorem shftidt
  let cA: class A
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  assume shftfval.1: |- F e. _V


  assert |- ( A e. CC -> ( ( F shift 0 ) ` A ) = ( F ` A ) )

  proof
    cA
    cc
    wcel
    cA
    cF
    cc0
    cshi
    co
    #
    cfv
    cA
    cF
    cc
    cres
    #
    cfv
    cA
    cF
    cfv
    cA
    @0
    @1
    cF
    shftfval.1
    shftidt2
    fveq1i
    cA
    cc
    cF
    fvres
    syl5eq
end
