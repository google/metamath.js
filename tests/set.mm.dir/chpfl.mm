include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "csu.mm"
include "cchp.mm"
include "flidm.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "wceq.mm"
include "reflcl.mm"
include "chpval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem chpfl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( A e. RR -> ( psi ` ( |_ ` A ) ) = ( psi ` A ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    cfl
    cfv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vx
    cv
    cvma
    cfv
    #
    vx
    csu
    #
    c1
    @1
    cfz
    co
    #
    @4
    vx
    csu
    @1
    cchp
    cfv
    #
    cA
    cchp
    cfv
    @0
    @3
    @6
    @4
    vx
    @0
    @2
    @1
    c1
    cfz
    cA
    flidm
    oveq2d
    sumeq1d
    @0
    @1
    cr
    wcel
    @7
    @5
    wceq
    cA
    reflcl
    @1
    vx
    chpval
    syl
    cA
    vx
    chpval
    3eqtr4d
end
