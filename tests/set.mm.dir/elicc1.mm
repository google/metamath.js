include "cle.mm"
include "cicc.mm"
include "df-icc.mm"
include "elixx1.mm"

theorem elicc1
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( C e. ( A [,] B ) <-> ( C e. RR* /\ A <_ C /\ C <_ B ) ) )

  proof
    vx
    vy
    vz
    cA
    cB
    cC
    cle
    cle
    cicc
    vx
    vy
    vz
    df-icc
    elixx1
end
