include "cdif.mm"
include "cun.mm"
include "csymdif.mm"
include "uncom.mm"
include "df-symdif.mm"
include "3eqtr4i.mm"

theorem symdifcom
  let cA: class A
  let cB: class B


  assert |- ( A /_\ B ) = ( B /_\ A )

  proof
    cA
    cB
    cdif
    #
    cB
    cA
    cdif
    #
    cun
    @1
    @0
    cun
    cA
    cB
    csymdif
    cB
    cA
    csymdif
    @0
    @1
    uncom
    cA
    cB
    df-symdif
    cB
    cA
    df-symdif
    3eqtr4i
end
