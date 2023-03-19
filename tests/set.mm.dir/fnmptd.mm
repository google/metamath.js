include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "fnmpt.mm"
include "syl.mm"

theorem fnmptd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  assume fnmptd.1: |- F/ x ph
  assume fnmptd.2: |- ( ( ph /\ x e. A ) -> B e. V )
  assume fnmptd.3: |- F = ( x e. A |-> B )

  disjoint A x
  assert |- ( ph -> F Fn A )

  proof
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    cF
    cA
    wfn
    wph
    @0
    vx
    cA
    fnmptd.1
    wph
    vx
    cv
    cA
    wcel
    @0
    fnmptd.2
    ex
    ralrimi
    vx
    cA
    cB
    cF
    cV
    fnmptd.3
    fnmpt
    syl
end
