include "clt.mm"
include "cle.mm"
include "cioc.mm"
include "df-ioc.mm"
include "elixx1.mm"

theorem elioc1
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( C e. ( A (,] B ) <-> ( C e. RR* /\ A < C /\ C <_ B ) ) )

  proof
    vx
    vy
    vz
    cA
    cB
    cC
    clt
    cle
    cioc
    vx
    vy
    vz
    df-ioc
    elixx1
end
