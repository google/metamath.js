include "wceq.mm"
include "cdif.mm"
include "cun.mm"
include "csymdif.mm"
include "difeq1.mm"
include "difeq2.mm"
include "uneq12d.mm"
include "df-symdif.mm"
include "3eqtr4g.mm"

theorem symdifeq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A /_\ C ) = ( B /_\ C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    cdif
    #
    cC
    cA
    cdif
    #
    cun
    cB
    cC
    cdif
    #
    cC
    cB
    cdif
    #
    cun
    cA
    cC
    csymdif
    cB
    cC
    csymdif
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    cC
    difeq1
    cA
    cB
    cC
    difeq2
    uneq12d
    cA
    cC
    df-symdif
    cB
    cC
    df-symdif
    3eqtr4g
end
