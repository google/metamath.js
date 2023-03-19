include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "dffn5.mm"
include "sylib.mm"

theorem feqmptd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cC: class C
  assume feqmptd.1: |- ( ph -> F : A --> B )

  disjoint A x
  disjoint F x
  disjoint C x
  assert |- ( ph -> F = ( x e. A |-> ( F ` x ) ) )

  proof
    wph
    cF
    cA
    wfn
    #
    cF
    vx
    cA
    vx
    cv
    cF
    cfv
    cmpt
    wceq
    wph
    cA
    cB
    cF
    wf
    @0
    feqmptd.1
    cA
    cB
    cF
    ffn
    syl
    vx
    cA
    cF
    dffn5
    sylib
end
