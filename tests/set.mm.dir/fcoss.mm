include "wf.mm"
include "ccom.mm"
include "fssd.mm"
include "fco.mm"
include "syl2anc.mm"

theorem fcoss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume fcoss.f: |- ( ph -> F : A --> B )
  assume fcoss.c: |- ( ph -> C C_ A )
  assume fcoss.g: |- ( ph -> G : D --> C )


  assert |- ( ph -> ( F o. G ) : D --> B )

  proof
    wph
    cA
    cB
    cF
    wf
    cD
    cA
    cG
    wf
    cD
    cB
    cF
    cG
    ccom
    wf
    fcoss.f
    wph
    cD
    cC
    cA
    cG
    fcoss.g
    fcoss.c
    fssd
    cD
    cA
    cB
    cF
    cG
    fco
    syl2anc
end
