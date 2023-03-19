include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "ex.mm"
include "ralrimi.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem ssdf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssdf.1: |- F/ x ph
  assume ssdf.2: |- ( ( ph /\ x e. A ) -> x e. B )

  disjoint A x
  disjoint B x
  assert |- ( ph -> A C_ B )

  proof
    wph
    vx
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    cA
    cB
    wss
    wph
    @1
    vx
    cA
    ssdf.1
    wph
    @0
    cA
    wcel
    @1
    ssdf.2
    ex
    ralrimi
    vx
    cA
    cB
    dfss3
    sylibr
end
