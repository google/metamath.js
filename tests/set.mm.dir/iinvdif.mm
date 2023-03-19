include "cvv.mm"
include "cdif.mm"
include "ciin.mm"
include "ciun.mm"
include "wceq.mm"
include "c0.mm"
include "dif0.mm"
include "0iun.mm"
include "difeq2i.mm"
include "0iin.mm"
include "3eqtr4ri.mm"
include "iineq1.mm"
include "iuneq1.mm"
include "difeq2d.mm"
include "3eqtr4a.mm"
include "iindif2.mm"
include "pm2.61ine.mm"

theorem iinvdif
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- |^|_ x e. A ( _V \ B ) = ( _V \ U_ x e. A B )

  proof
    vx
    cA
    cvv
    cB
    cdif
    #
    ciin
    #
    cvv
    vx
    cA
    cB
    ciun
    #
    cdif
    #
    wceq
    cA
    c0
    cA
    c0
    wceq
    #
    vx
    c0
    @0
    ciin
    #
    cvv
    vx
    c0
    cB
    ciun
    #
    cdif
    #
    @1
    @3
    cvv
    c0
    cdif
    cvv
    @7
    @5
    cvv
    dif0
    @6
    c0
    cvv
    vx
    cB
    0iun
    difeq2i
    vx
    @0
    0iin
    3eqtr4ri
    vx
    cA
    c0
    @0
    iineq1
    @4
    @2
    @6
    cvv
    vx
    cA
    c0
    cB
    iuneq1
    difeq2d
    3eqtr4a
    vx
    cA
    cvv
    cB
    iindif2
    pm2.61ine
end
