include "cv.mm"
include "wcel.mm"
include "biimpd.mm"
include "ssrd.mm"
include "biimprd.mm"
include "eqssd.mm"

theorem eqrdOLD
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume eqrd.0: |- F/ x ph
  assume eqrd.1: |- F/_ x A
  assume eqrd.2: |- F/_ x B
  assume eqrd.3: |- ( ph -> ( x e. A <-> x e. B ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    wph
    vx
    cA
    cB
    eqrd.0
    eqrd.1
    eqrd.2
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    eqrd.3
    biimpd
    ssrd
    wph
    vx
    cB
    cA
    eqrd.0
    eqrd.2
    eqrd.1
    wph
    @1
    @2
    eqrd.3
    biimprd
    ssrd
    eqssd
end
