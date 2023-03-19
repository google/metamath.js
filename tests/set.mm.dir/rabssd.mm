include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "3exp.mm"
include "ralrimi.mm"
include "rabssf.mm"
include "sylibr.mm"

theorem rabssd
  let wph: wff ph
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabssd.1: |- F/ x ph
  assume rabssd.2: |- F/_ x B
  assume rabssd.3: |- ( ( ph /\ x e. A /\ ch ) -> x e. B )


  assert |- ( ph -> { x e. A | ch } C_ B )

  proof
    wph
    wch
    vx
    cv
    #
    cB
    wcel
    #
    wi
    #
    vx
    cA
    wral
    wch
    vx
    cA
    crab
    cB
    wss
    wph
    @2
    vx
    cA
    rabssd.1
    wph
    @0
    cA
    wcel
    wch
    @1
    rabssd.3
    3exp
    ralrimi
    wch
    vx
    cA
    cB
    rabssd.2
    rabssf
    sylibr
end
