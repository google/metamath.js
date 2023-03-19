include "cico.mm"
include "clt.mm"
include "cle.mm"
include "cioo.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "cv.mm"
include "xrltle.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "idd.mm"
include "ixxssixx.mm"

theorem ioossico
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x
  let cC: class C
  let cD: class D


  assert |- ( A (,) B ) C_ ( A [,) B )

  proof
    va
    vb
    vx
    vw
    cA
    cB
    cico
    clt
    clt
    cle
    clt
    cioo
    va
    vb
    vx
    df-ioo
    va
    vb
    vx
    df-ico
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
    clt
    wbr
    idd
    ixxssixx
end
