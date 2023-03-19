include "con0.mm"
include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "ciun.mm"
include "omlim.mm"
include "eleq2d.mm"
include "eliun.mm"
include "syl6bb.mm"
include "biimpa.mm"

theorem omordlim
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint A z
  disjoint v w
  disjoint A w
  disjoint A v
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint C y
  assert |- ( ( ( A e. On /\ ( B e. D /\ Lim B ) ) /\ C e. ( A .o B ) ) -> E. x e. B C e. ( A .o x ) )

  proof
    cA
    con0
    wcel
    cB
    cD
    wcel
    cB
    wlim
    wa
    wa
    #
    cC
    cA
    cB
    comu
    co
    #
    wcel
    #
    cC
    cA
    vx
    cv
    comu
    co
    #
    wcel
    vx
    cB
    wrex
    #
    @0
    @2
    cC
    vx
    cB
    @3
    ciun
    #
    wcel
    @4
    @0
    @1
    @5
    cC
    vx
    cA
    cB
    cD
    omlim
    eleq2d
    vx
    cC
    cB
    @3
    eliun
    syl6bb
    biimpa
end
