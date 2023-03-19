include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cmpt2.mm"
include "3expb.mm"
include "eqeq2d.mm"
include "pm5.32da.mm"
include "oprabbidv.mm"
include "df-mpt2.mm"
include "3eqtr4g.mm"

theorem mpt2eq3dva
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vz: setvar z
  assume mpt2eq3dva.1: |- ( ( ph /\ x e. A /\ y e. B ) -> C = D )

  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint ph z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  assert |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wa
    #
    vz
    cv
    #
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    @2
    @3
    cD
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vx
    vy
    cA
    cB
    cD
    cmpt2
    wph
    @5
    @7
    vx
    vy
    vz
    wph
    @2
    @4
    @6
    wph
    @2
    wa
    cC
    cD
    @3
    wph
    @0
    @1
    cC
    cD
    wceq
    mpt2eq3dva.1
    3expb
    eqeq2d
    pm5.32da
    oprabbidv
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    vx
    vy
    vz
    cA
    cB
    cD
    df-mpt2
    3eqtr4g
end
