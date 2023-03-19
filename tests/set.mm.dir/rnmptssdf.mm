include "wcel.mm"
include "wral.mm"
include "crn.mm"
include "wss.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "rnmptssf.mm"
include "syl.mm"

theorem rnmptssdf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume rnmptssdf.1: |- F/ x ph
  assume rnmptssdf.2: |- F/_ x C
  assume rnmptssdf.3: |- F = ( x e. A |-> B )
  assume rnmptssdf.4: |- ( ( ph /\ x e. A ) -> B e. C )

  disjoint A x
  assert |- ( ph -> ran F C_ C )

  proof
    wph
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    cF
    crn
    cC
    wss
    wph
    @0
    vx
    cA
    rnmptssdf.1
    wph
    vx
    cv
    cA
    wcel
    @0
    rnmptssdf.4
    ex
    ralrimi
    vx
    cA
    cB
    cC
    cF
    rnmptssdf.2
    rnmptssdf.3
    rnmptssf
    syl
end
