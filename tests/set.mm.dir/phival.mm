include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "cphi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rabeqbidv.mm"
include "fveq2d.mm"
include "df-phi.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem phival
  let vx: setvar x
  let cN: class N
  let vn: setvar n

  disjoint N x
  disjoint n x
  disjoint N n
  assert |- ( N e. NN -> ( phi ` N ) = ( # ` { x e. ( 1 ... N ) | ( x gcd N ) = 1 } ) )

  proof
    vn
    cN
    vx
    cv
    #
    vn
    cv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    vx
    c1
    @1
    cfz
    co
    #
    crab
    #
    chash
    cfv
    @0
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    vx
    c1
    cN
    cfz
    co
    #
    crab
    #
    chash
    cfv
    cn
    cphi
    @1
    cN
    wceq
    #
    @5
    @9
    chash
    @10
    @3
    @7
    vx
    @4
    @8
    @1
    cN
    c1
    cfz
    oveq2
    @10
    @2
    @6
    c1
    @1
    cN
    @0
    cgcd
    oveq2
    eqeq1d
    rabeqbidv
    fveq2d
    vx
    vn
    df-phi
    @9
    chash
    fvex
    fvmpt
end
