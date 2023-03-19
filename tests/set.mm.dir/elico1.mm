include "cle.mm"
include "clt.mm"
include "cico.mm"
include "df-ico.mm"
include "elixx1.mm"

theorem elico1
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( C e. ( A [,) B ) <-> ( C e. RR* /\ A <_ C /\ C < B ) ) )

  proof
    vx
    vy
    vz
    cA
    cB
    cC
    cle
    clt
    cico
    vx
    vy
    vz
    df-ico
    elixx1
end
