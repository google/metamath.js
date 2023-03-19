include "hhnv.mm"
include "hhba.mm"
include "h2hmetdval.mm"

theorem hhmetdval
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.
  assume hhims2.2: |- D = ( IndMet ` U )


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A D B ) = ( normh ` ( A -h B ) ) )

  proof
    cA
    cB
    cD
    cU
    hhnv.1
    cU
    hhnv.1
    hhnv
    cU
    hhnv.1
    hhba
    hhims2.2
    h2hmetdval
end
