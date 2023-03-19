include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wex.mm"
include "wa.mm"
include "elisset.mm"
include "wmo.mm"
include "moeq.mm"
include "a1i.mm"
include "cmpt2.mm"
include "coprab.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "ovidi.mm"
include "eqeq2.mm"
include "mpbidi.mm"
include "exlimdv.mm"
include "syl5.mm"
include "3impia.mm"

theorem ovmpt4g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vz: setvar z
  assume ovmpt4g.3: |- F = ( x e. A , y e. B |-> C )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint F z
  assert |- ( ( x e. A /\ y e. B /\ C e. V ) -> ( x F y ) = C )

  proof
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
    cC
    cV
    wcel
    #
    @0
    @2
    cF
    co
    #
    cC
    wceq
    #
    @4
    vz
    cv
    #
    cC
    wceq
    #
    vz
    wex
    @1
    @3
    wa
    #
    @6
    vz
    cC
    cV
    elisset
    @9
    @8
    @6
    vz
    @8
    @5
    @7
    wceq
    @6
    @9
    @8
    vx
    vy
    vz
    cA
    cB
    cF
    @8
    vz
    wmo
    @9
    vz
    cC
    moeq
    a1i
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    @9
    @8
    wa
    vx
    vy
    vz
    coprab
    ovmpt4g.3
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    eqtri
    ovidi
    @7
    cC
    @5
    eqeq2
    mpbidi
    exlimdv
    syl5
    3impia
end
