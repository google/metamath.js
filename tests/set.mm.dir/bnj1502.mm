include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "funssfv.mm"
include "syl3anc.mm"

theorem bnj1502
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  assume bnj1502.1: |- ( ph -> Fun F )
  assume bnj1502.2: |- ( ph -> G C_ F )
  assume bnj1502.3: |- ( ph -> A e. dom G )


  assert |- ( ph -> ( F ` A ) = ( G ` A ) )

  proof
    wph
    cF
    wfun
    cG
    cF
    wss
    cA
    cG
    cdm
    wcel
    cA
    cF
    cfv
    cA
    cG
    cfv
    wceq
    bnj1502.1
    bnj1502.2
    bnj1502.3
    cA
    cF
    cG
    funssfv
    syl3anc
end
