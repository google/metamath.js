include "cint.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "ex.mm"
include "ralrimi.mm"
include "wb.mm"
include "elintg.mm"
include "syl.mm"
include "mpbird.mm"

theorem elintd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume elintd.1: |- F/ x ph
  assume elintd.2: |- ( ph -> A e. V )
  assume elintd.3: |- ( ( ph /\ x e. B ) -> A e. x )

  disjoint A x
  disjoint B x
  assert |- ( ph -> A e. |^| B )

  proof
    wph
    cA
    cB
    cint
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cB
    wral
    #
    wph
    @2
    vx
    cB
    elintd.1
    wph
    @1
    cB
    wcel
    @2
    elintd.3
    ex
    ralrimi
    wph
    cA
    cV
    wcel
    @0
    @3
    wb
    elintd.2
    vx
    cA
    cB
    cV
    elintg
    syl
    mpbird
end
