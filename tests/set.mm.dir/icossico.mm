include "cico.mm"
include "cle.mm"
include "clt.mm"
include "df-ico.mm"
include "cv.mm"
include "xrletr.mm"
include "xrltletr.mm"
include "ixxss12.mm"

theorem icossico
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( A <_ C /\ D <_ B ) ) -> ( C [,) D ) C_ ( A [,) B ) )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cico
    cle
    clt
    cle
    clt
    cico
    cle
    cle
    vx
    vy
    vz
    df-ico
    #
    @0
    cA
    cC
    vw
    cv
    #
    xrletr
    @1
    cD
    cB
    xrltletr
    ixxss12
end
