include "cicc.mm"
include "clt.mm"
include "cle.mm"
include "cioc.mm"
include "df-ioc.mm"
include "df-icc.mm"
include "cv.mm"
include "xrltle.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "idd.mm"
include "ixxssixx.mm"

theorem iocssicc
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x
  let cC: class C
  let cD: class D


  assert |- ( A (,] B ) C_ ( A [,] B )

  proof
    va
    vb
    vx
    vw
    cA
    cB
    cicc
    clt
    cle
    cle
    cle
    cioc
    va
    vb
    vx
    df-ioc
    va
    vb
    vx
    df-icc
    cA
    vw
    cv
    #
    xrltle
    @0
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    @0
    cB
    cle
    wbr
    idd
    ixxssixx
end
