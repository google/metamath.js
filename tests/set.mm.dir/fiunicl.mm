include "cuni.mm"
include "cv.mm"
include "ciun.mm"
include "uniiun.mm"
include "nfv.mm"
include "wcel.mm"
include "simpr.mm"
include "fiiuncl.mm"
include "syl5eqel.mm"

theorem fiunicl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume fiunicl.1: |- ( ( ph /\ x e. A /\ y e. A ) -> ( x u. y ) e. A )
  assume fiunicl.2: |- ( ph -> A e. Fin )
  assume fiunicl.3: |- ( ph -> A =/= (/) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( ph -> U. A e. A )

  proof
    wph
    cA
    cuni
    vz
    cA
    vz
    cv
    #
    ciun
    cA
    vz
    cA
    uniiun
    wph
    vz
    vx
    vy
    cA
    @0
    cA
    wph
    vz
    nfv
    wph
    @0
    cA
    wcel
    simpr
    fiunicl.1
    fiunicl.2
    fiunicl.3
    fiiuncl
    syl5eqel
end
