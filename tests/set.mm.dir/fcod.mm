include "wf.mm"
include "ccom.mm"
include "fco.mm"
include "syl2anc.mm"

theorem fcod
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  assume fcod.1: |- ( ph -> F : B --> C )
  assume fcod.2: |- ( ph -> G : A --> B )


  assert |- ( ph -> ( F o. G ) : A --> C )

  proof
    wph
    cB
    cC
    cF
    wf
    cA
    cB
    cG
    wf
    cA
    cC
    cF
    cG
    ccom
    wf
    fcod.1
    fcod.2
    cA
    cB
    cC
    cF
    cG
    fco
    syl2anc
end
