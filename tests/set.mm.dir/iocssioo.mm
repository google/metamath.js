include "cioc.mm"
include "clt.mm"
include "cle.mm"
include "cioo.mm"
include "df-ioo.mm"
include "df-ioc.mm"
include "cv.mm"
include "xrlelttr.mm"
include "ixxss12.mm"

theorem iocssioo
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( A <_ C /\ D < B ) ) -> ( C (,] D ) C_ ( A (,) B ) )

  proof
    va
    vb
    vx
    vw
    cA
    cB
    cC
    cD
    cioc
    clt
    clt
    clt
    cle
    cioo
    cle
    clt
    va
    vb
    vx
    df-ioo
    va
    vb
    vx
    df-ioc
    cA
    cC
    vw
    cv
    #
    xrlelttr
    @0
    cD
    cB
    xrlelttr
    ixxss12
end
