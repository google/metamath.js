include "cioo.mm"
include "clt.mm"
include "cle.mm"
include "df-ioo.mm"
include "cv.mm"
include "xrlelttr.mm"
include "xrltletr.mm"
include "ixxss12.mm"

theorem ioossioo
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( A <_ C /\ D <_ B ) ) -> ( C (,) D ) C_ ( A (,) B ) )

  proof
    va
    vb
    vx
    vw
    cA
    cB
    cC
    cD
    cioo
    clt
    clt
    clt
    clt
    cioo
    cle
    cle
    va
    vb
    vx
    df-ioo
    #
    @0
    cA
    cC
    vw
    cv
    #
    xrlelttr
    @1
    cD
    cB
    xrltletr
    ixxss12
end
