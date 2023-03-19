include "cfn.mm"
include "wcel.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "ssfi.mm"
include "syl2anc.mm"

theorem fisuppfi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fisuppfi.1: |- ( ph -> A e. Fin )
  assume fisuppfi.2: |- ( ph -> F : A --> B )


  assert |- ( ph -> ( `' F " C ) e. Fin )

  proof
    wph
    cA
    cfn
    wcel
    cF
    ccnv
    cC
    cima
    #
    cA
    wss
    @0
    cfn
    wcel
    fisuppfi.1
    wph
    cF
    cdm
    #
    @0
    cA
    cF
    cC
    cnvimass
    wph
    cA
    cB
    cF
    wf
    @1
    cA
    wceq
    fisuppfi.2
    cA
    cB
    cF
    fdm
    syl
    syl5sseq
    cA
    @0
    ssfi
    syl2anc
end
