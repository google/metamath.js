include "wf.mm"
include "crn.mm"
include "wss.mm"
include "frn.mm"
include "syl.mm"

theorem frnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume frnd.1: |- ( ph -> F : A --> B )


  assert |- ( ph -> ran F C_ B )

  proof
    wph
    cA
    cB
    cF
    wf
    cF
    crn
    cB
    wss
    frnd.1
    cA
    cB
    cF
    frn
    syl
end
