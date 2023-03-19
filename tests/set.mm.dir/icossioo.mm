include "cico.mm"
include "clt.mm"
include "cle.mm"
include "cioo.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "cv.mm"
include "xrltletr.mm"
include "ixxss12.mm"

theorem icossioo
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( A < C /\ D <_ B ) ) -> ( C [,) D ) C_ ( A (,) B ) )

  proof
    va
    vb
    vx
    vw
    cA
    cB
    cC
    cD
    cico
    clt
    clt
    cle
    clt
    cioo
    clt
    cle
    va
    vb
    vx
    df-ioo
    va
    vb
    vx
    df-ico
    cA
    cC
    vw
    cv
    #
    xrltletr
    @0
    cD
    cB
    xrltletr
    ixxss12
end
