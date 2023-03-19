include "wfn.mm"
include "wss.mm"
include "wcel.mm"
include "cfv.mm"
include "cima.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "ssid.mm"
include "a1i.mm"
include "fnfvima.mm"
include "syl3anc.mm"

theorem wfximgfd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume wfximgfd.1: |- ( ph -> C e. A )
  assume wfximgfd.2: |- ( ph -> F : A --> B )


  assert |- ( ph -> ( F ` C ) e. ( F " A ) )

  proof
    wph
    cF
    cA
    wfn
    #
    cA
    cA
    wss
    #
    cC
    cA
    wcel
    cC
    cF
    cfv
    cF
    cA
    cima
    wcel
    wph
    cA
    cB
    cF
    wf
    @0
    wfximgfd.2
    cA
    cB
    cF
    ffn
    syl
    @1
    wph
    cA
    ssid
    a1i
    wfximgfd.1
    cA
    cA
    cF
    cC
    fnfvima
    syl3anc
end
