include "wsmo.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wrex.mm"
include "eliun.mm"
include "con0.mm"
include "wi.mm"
include "smofvon.mm"
include "smoel.mm"
include "3expia.mm"
include "ontr1.mm"
include "expcomd.mm"
include "sylsyld.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem smoiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let cC: class C
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  assert |- ( ( Smo B /\ A e. dom B ) -> U_ x e. A ( B ` x ) C_ ( B ` A ) )

  proof
    cB
    wsmo
    #
    cA
    cB
    cdm
    wcel
    #
    wa
    #
    vy
    vx
    cA
    vx
    cv
    #
    cB
    cfv
    #
    ciun
    #
    cA
    cB
    cfv
    #
    vy
    cv
    #
    @5
    wcel
    @7
    @4
    wcel
    #
    vx
    cA
    wrex
    @2
    @7
    @6
    wcel
    #
    vx
    @7
    cA
    @4
    eliun
    @2
    @8
    @9
    vx
    cA
    @2
    @6
    con0
    wcel
    #
    @3
    cA
    wcel
    #
    @4
    @6
    wcel
    #
    @8
    @9
    wi
    cA
    cB
    smofvon
    @0
    @1
    @11
    @12
    cA
    cB
    @3
    smoel
    3expia
    @10
    @8
    @12
    @9
    @7
    @4
    @6
    ontr1
    expcomd
    sylsyld
    rexlimdv
    syl5bi
    ssrdv
end
