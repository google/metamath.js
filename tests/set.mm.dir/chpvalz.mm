include "cz.mm"
include "wcel.mm"
include "cchp.mm"
include "cfv.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "csu.mm"
include "cr.mm"
include "wceq.mm"
include "zre.mm"
include "chpval.mm"
include "syl.mm"
include "flid.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "eqtrd.mm"

theorem chpvalz
  let vn: setvar n
  let cN: class N
  let vi: setvar i

  disjoint N n
  disjoint i n
  assert |- ( N e. ZZ -> ( psi ` N ) = sum_ n e. ( 1 ... N ) ( Lam ` n ) )

  proof
    cN
    cz
    wcel
    #
    cN
    cchp
    cfv
    #
    c1
    cN
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    cvma
    cfv
    #
    vn
    csu
    #
    c1
    cN
    cfz
    co
    #
    @4
    vn
    csu
    @0
    cN
    cr
    wcel
    @1
    @5
    wceq
    cN
    zre
    cN
    vn
    chpval
    syl
    @0
    @3
    @6
    @4
    vn
    @0
    @2
    cN
    c1
    cfz
    cN
    flid
    oveq2d
    sumeq1d
    eqtrd
end
