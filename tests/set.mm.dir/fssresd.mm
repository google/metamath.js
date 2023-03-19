include "wf.mm"
include "wss.mm"
include "cres.mm"
include "fssres.mm"
include "syl2anc.mm"

theorem fssresd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fssresd.1: |- ( ph -> F : A --> B )
  assume fssresd.2: |- ( ph -> C C_ A )


  assert |- ( ph -> ( F |` C ) : C --> B )

  proof
    wph
    cA
    cB
    cF
    wf
    cC
    cA
    wss
    cC
    cB
    cF
    cC
    cres
    wf
    fssresd.1
    fssresd.2
    cA
    cB
    cC
    cF
    fssres
    syl2anc
end
