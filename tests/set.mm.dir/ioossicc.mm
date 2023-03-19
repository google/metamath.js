include "cicc.mm"
include "clt.mm"
include "cle.mm"
include "cioo.mm"
include "df-ioo.mm"
include "df-icc.mm"
include "cv.mm"
include "xrltle.mm"
include "ixxssixx.mm"

theorem ioossicc
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A (,) B ) C_ ( A [,] B )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cicc
    clt
    clt
    cle
    cle
    cioo
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-icc
    cA
    vw
    cv
    #
    xrltle
    @0
    cB
    xrltle
    ixxssixx
end
