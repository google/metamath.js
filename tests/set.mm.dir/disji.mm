include "wcel.mm"
include "wa.mm"
include "wdisj.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "inelcm.mm"
include "disji2.mm"
include "3expia.mm"
include "necon1d.mm"
include "3impia.mm"
include "syl3an3.mm"

theorem disji
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  assume disji.1: |- ( x = X -> B = C )
  assume disji.2: |- ( x = Y -> B = D )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint X x
  disjoint Y x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D z
  disjoint X y
  disjoint X z
  disjoint Y z
  assert |- ( ( Disj_ x e. A B /\ ( X e. A /\ Y e. A ) /\ ( Z e. C /\ Z e. D ) ) -> X = Y )

  proof
    cZ
    cC
    wcel
    cZ
    cD
    wcel
    wa
    vx
    cA
    cB
    wdisj
    #
    cX
    cA
    wcel
    cY
    cA
    wcel
    wa
    #
    cC
    cD
    cin
    #
    c0
    wne
    #
    cX
    cY
    wceq
    #
    cZ
    cC
    cD
    inelcm
    @0
    @1
    @3
    @4
    @0
    @1
    wa
    cX
    cY
    @2
    c0
    @0
    @1
    cX
    cY
    wne
    @2
    c0
    wceq
    vx
    cA
    cB
    cC
    cD
    cX
    cY
    disji.1
    disji.2
    disji2
    3expia
    necon1d
    3impia
    syl3an3
end
