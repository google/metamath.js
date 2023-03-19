include "cicc.mm"
include "cle.mm"
include "clt.mm"
include "cico.mm"
include "df-ico.mm"
include "df-icc.mm"
include "cxr.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxssixx.mm"

theorem icossicc
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x
  let cC: class C
  let cD: class D


  assert |- ( A [,) B ) C_ ( A [,] B )

  proof
    va
    vb
    vx
    vw
    cA
    cB
    cicc
    cle
    clt
    cle
    cle
    cico
    va
    vb
    vx
    df-ico
    va
    vb
    vx
    df-icc
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
    cle
    wbr
    idd
    @0
    cB
    xrltle
    ixxssixx
end
