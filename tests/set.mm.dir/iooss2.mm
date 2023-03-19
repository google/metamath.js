include "cioo.mm"
include "clt.mm"
include "cle.mm"
include "df-ioo.mm"
include "cv.mm"
include "xrltletr.mm"
include "ixxss2.mm"

theorem iooss2
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( C e. RR* /\ B <_ C ) -> ( A (,) B ) C_ ( A (,) C ) )

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
    vw
    cv
    cB
    cC
    xrltletr
    ixxss2
end
