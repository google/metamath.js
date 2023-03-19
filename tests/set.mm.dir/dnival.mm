include "cv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "cr.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem dnival
  let vx: setvar x
  let cA: class A
  let cT: class T
  assume dnival.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )

  disjoint A x
  assert |- ( A e. RR -> ( T ` A ) = ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) )

  proof
    vx
    cA
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    cA
    @1
    caddc
    co
    #
    cfl
    cfv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    cr
    cT
    @0
    cA
    wceq
    #
    @4
    @7
    cabs
    @8
    @3
    @6
    @0
    cA
    cmin
    @8
    @2
    @5
    cfl
    @0
    cA
    @1
    caddc
    oveq1
    fveq2d
    @8
    id
    oveq12d
    fveq2d
    dnival.1
    @7
    cabs
    fvex
    fvmpt
end
