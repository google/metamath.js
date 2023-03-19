include "cv.mm"
include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cpjh.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "jplem1.mm"
include "cch.mm"
include "strlem2.mm"
include "ax-mp.mm"
include "eqeq1i.mm"
include "syl6bbr.mm"

theorem jplem2
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cB: class B
  assume jp.1: |- S = ( x e. CH |-> ( ( normh ` ( ( projh ` x ) ` u ) ) ^ 2 ) )
  assume jp.2: |- A e. CH

  disjoint u x
  disjoint A x
  disjoint B x
  assert |- ( ( u e. ~H /\ ( normh ` u ) = 1 ) -> ( u e. A <-> ( S ` A ) = 1 ) )

  proof
    vu
    cv
    #
    chil
    wcel
    @0
    cno
    cfv
    c1
    wceq
    wa
    @0
    cA
    wcel
    @0
    cA
    cpjh
    cfv
    cfv
    cno
    cfv
    c2
    cexp
    co
    #
    c1
    wceq
    cA
    cS
    cfv
    #
    c1
    wceq
    vu
    cA
    jp.2
    jplem1
    @2
    @1
    c1
    cA
    cch
    wcel
    @2
    @1
    wceq
    jp.2
    vx
    vu
    cA
    cS
    jp.1
    strlem2
    ax-mp
    eqeq1i
    syl6bbr
end
