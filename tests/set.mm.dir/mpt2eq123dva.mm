include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cmpt2.mm"
include "eqeq2d.mm"
include "pm5.32da.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "oprabbidv.mm"
include "df-mpt2.mm"
include "3eqtr4g.mm"

theorem mpt2eq123dva
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vz: setvar z
  assume mpt2eq123dv.1: |- ( ph -> A = D )
  assume mpt2eq123dva.2: |- ( ( ph /\ x e. A ) -> B = E )
  assume mpt2eq123dva.3: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C = F )

  disjoint ph x
  disjoint ph y
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint E z
  disjoint x z
  disjoint ph z
  disjoint F z
  disjoint y z
  assert |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
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
    @0
    cD
    wcel
    #
    @2
    cE
    wcel
    #
    wa
    #
    @5
    cF
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
    cD
    cE
    cF
    cmpt2
    wph
    @7
    @12
    vx
    vy
    vz
    wph
    @7
    @4
    @11
    wa
    @12
    wph
    @4
    @6
    @11
    wph
    @4
    wa
    cC
    cF
    @5
    mpt2eq123dva.3
    eqeq2d
    pm5.32da
    wph
    @4
    @10
    @11
    wph
    @4
    @1
    @9
    wa
    @10
    wph
    @1
    @3
    @9
    wph
    @1
    wa
    cB
    cE
    @2
    mpt2eq123dva.2
    eleq2d
    pm5.32da
    wph
    @1
    @8
    @9
    wph
    cA
    cD
    @0
    mpt2eq123dv.1
    eleq2d
    anbi1d
    bitrd
    anbi1d
    bitrd
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
    cD
    cE
    cF
    df-mpt2
    3eqtr4g
end
