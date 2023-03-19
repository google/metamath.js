include "wcel.mm"
include "wa.mm"
include "wdisj.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "inelcm.mm"
include "disji2f.mm"
include "3expia.mm"
include "necon1d.mm"
include "3impia.mm"
include "syl3an3.mm"

theorem disjif
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  assume disjif.1: |- F/_ x C
  assume disjif.2: |- ( x = Y -> B = C )

  disjoint A x
  disjoint Y x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint Y z
  assert |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\ ( Z e. B /\ Z e. C ) ) -> x = Y )

  proof
    cZ
    cB
    wcel
    cZ
    cC
    wcel
    wa
    vx
    cA
    cB
    wdisj
    #
    vx
    cv
    #
    cA
    wcel
    cY
    cA
    wcel
    wa
    #
    cB
    cC
    cin
    #
    c0
    wne
    #
    @1
    cY
    wceq
    #
    cZ
    cB
    cC
    inelcm
    @0
    @2
    @4
    @5
    @0
    @2
    wa
    @1
    cY
    @3
    c0
    @0
    @2
    @1
    cY
    wne
    @3
    c0
    wceq
    vx
    cA
    cB
    cC
    cY
    disjif.1
    disjif.2
    disji2f
    3expia
    necon1d
    3impia
    syl3an3
end
