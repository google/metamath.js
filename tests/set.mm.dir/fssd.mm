include "wf.mm"
include "wss.mm"
include "fss.mm"
include "syl2anc.mm"

theorem fssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fssd.f: |- ( ph -> F : A --> B )
  assume fssd.b: |- ( ph -> B C_ C )


  assert |- ( ph -> F : A --> C )

  proof
    wph
    cA
    cB
    cF
    wf
    cB
    cC
    wss
    cA
    cC
    cF
    wf
    fssd.f
    fssd.b
    cA
    cB
    cC
    cF
    fss
    syl2anc
end
