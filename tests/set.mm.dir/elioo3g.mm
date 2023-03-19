include "clt.mm"
include "cioo.mm"
include "df-ioo.mm"
include "elixx3g.mm"

theorem elioo3g
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( C e. ( A (,) B ) <-> ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A < C /\ C < B ) ) )

  proof
    vx
    vy
    vz
    cA
    cB
    cC
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    elixx3g
end
