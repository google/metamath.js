include "cioc.mm"
include "clt.mm"
include "cle.mm"
include "cioo.mm"
include "df-ioo.mm"
include "df-ioc.mm"
include "cxr.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxssixx.mm"

theorem ioossioc
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A (,) B ) C_ ( A (,] B )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cioc
    clt
    clt
    clt
    cle
    cioo
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-ioc
    cA
    cxr
    wcel
    vw
    cv
    #
    cxr
    wcel
    wa
    cA
    @0
    clt
    wbr
    idd
    @0
    cB
    xrltle
    ixxssixx
end
