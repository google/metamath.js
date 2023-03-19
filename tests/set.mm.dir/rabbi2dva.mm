include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "dfin5.mm"
include "rabbidva.mm"
include "syl5eq.mm"

theorem rabbi2dva
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabbi2dva.1: |- ( ( ph /\ x e. A ) -> ( x e. B <-> ps ) )

  disjoint ph x
  disjoint A x
  disjoint B x
  assert |- ( ph -> ( A i^i B ) = { x e. A | ps } )

  proof
    wph
    cA
    cB
    cin
    vx
    cv
    cB
    wcel
    #
    vx
    cA
    crab
    wps
    vx
    cA
    crab
    vx
    cA
    cB
    dfin5
    wph
    @0
    wps
    vx
    cA
    rabbi2dva.1
    rabbidva
    syl5eq
end
