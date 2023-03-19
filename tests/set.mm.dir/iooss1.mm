include "cioo.mm"
include "clt.mm"
include "cle.mm"
include "df-ioo.mm"
include "cv.mm"
include "xrlelttr.mm"
include "ixxss1.mm"

theorem iooss1
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( A e. RR* /\ A <_ B ) -> ( B (,) C ) C_ ( A (,) C ) )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cioo
    clt
    clt
    clt
    cioo
    cle
    vx
    vy
    vz
    df-ioo
    #
    @0
    cA
    cB
    vw
    cv
    xrlelttr
    ixxss1
end
