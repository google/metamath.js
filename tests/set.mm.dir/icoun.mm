include "cico.mm"
include "cle.mm"
include "clt.mm"
include "df-ico.mm"
include "cv.mm"
include "xrlenlt.mm"
include "xrltletr.mm"
include "xrletr.mm"
include "ixxun.mm"

theorem icoun
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A <_ B /\ B <_ C ) ) -> ( ( A [,) B ) u. ( B [,) C ) ) = ( A [,) C ) )

  proof
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cico
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
    cB
    vw
    cv
    #
    xrlenlt
    @0
    @1
    cB
    cC
    xrltletr
    cA
    cB
    @1
    xrletr
    ixxun
end
