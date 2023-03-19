include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"

theorem fdmd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume fdmd.1: |- ( ph -> F : A --> B )


  assert |- ( ph -> dom F = A )

  proof
    wph
    cA
    cB
    cF
    wf
    cF
    cdm
    cA
    wceq
    fdmd.1
    cA
    cB
    cF
    fdm
    syl
end
