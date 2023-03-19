include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "rexr.mm"
include "anim12i.mm"
include "df-icc.mm"
include "cv.mm"
include "xrletr.mm"
include "ixxss12.mm"
include "sylan.mm"

theorem iccss
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( A <_ C /\ D <_ B ) ) -> ( C [,] D ) C_ ( A [,] B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    cA
    cC
    cle
    wbr
    cD
    cB
    cle
    wbr
    wa
    cC
    cD
    cicc
    co
    cA
    cB
    cicc
    co
    wss
    @0
    @2
    @1
    @3
    cA
    rexr
    cB
    rexr
    anim12i
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cicc
    cle
    cle
    cle
    cle
    cicc
    cle
    cle
    vx
    vy
    vz
    df-icc
    #
    @4
    cA
    cC
    vw
    cv
    #
    xrletr
    @5
    cD
    cB
    xrletr
    ixxss12
    sylan
end
