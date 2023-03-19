include "cicc.mm"
include "cle.mm"
include "clt.mm"
include "cico.mm"
include "df-ico.mm"
include "df-icc.mm"
include "cv.mm"
include "xrletr.mm"
include "xrlelttr.mm"
include "ixxss12.mm"

theorem iccssico
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( A <_ C /\ D < B ) ) -> ( C [,] D ) C_ ( A [,) B ) )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cicc
    cle
    clt
    cle
    cle
    cico
    cle
    clt
    vx
    vy
    vz
    df-ico
    vx
    vy
    vz
    df-icc
    cA
    cC
    vw
    cv
    #
    xrletr
    @0
    cD
    cB
    xrlelttr
    ixxss12
end
