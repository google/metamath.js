include "ctpos.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "ancom.mm"
include "anbi1i.mm"
include "oprabbii.mm"
include "3eqtri.mm"
include "tposoprab.mm"
include "eqtr4i.mm"

theorem tposmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vz: setvar z
  assume tposmpt2.1: |- F = ( x e. A , y e. B |-> C )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  assert |- tpos F = ( y e. B , x e. A |-> C )

  proof
    cF
    ctpos
    vy
    cv
    cB
    wcel
    #
    vx
    cv
    cA
    wcel
    #
    wa
    #
    vz
    cv
    cC
    wceq
    #
    wa
    #
    vy
    vx
    vz
    coprab
    vy
    vx
    cB
    cA
    cC
    cmpt2
    @4
    vx
    vy
    vz
    cF
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    @1
    @0
    wa
    #
    @3
    wa
    #
    vx
    vy
    vz
    coprab
    @4
    vx
    vy
    vz
    coprab
    tposmpt2.1
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    @6
    @4
    vx
    vy
    vz
    @5
    @2
    @3
    @1
    @0
    ancom
    anbi1i
    oprabbii
    3eqtri
    tposoprab
    vy
    vx
    vz
    cB
    cA
    cC
    df-mpt2
    eqtr4i
end
