include "cicc.mm"
include "clt.mm"
include "cle.mm"
include "cioo.mm"
include "df-ioo.mm"
include "df-icc.mm"
include "cv.mm"
include "xrltletr.mm"
include "xrlelttr.mm"
include "ixxss12.mm"

theorem iccssioo
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( A < C /\ D < B ) ) -> ( C [,] D ) C_ ( A (,) B ) )

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
    clt
    clt
    cle
    cle
    cioo
    clt
    clt
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-icc
    cA
    cC
    vw
    cv
    #
    xrltletr
    @0
    cD
    cB
    xrlelttr
    ixxss12
end
