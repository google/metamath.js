include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "fun2ssres.mm"
include "syl3anc.mm"

theorem bnj1503
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  assume bnj1503.1: |- ( ph -> Fun F )
  assume bnj1503.2: |- ( ph -> G C_ F )
  assume bnj1503.3: |- ( ph -> A C_ dom G )


  assert |- ( ph -> ( F |` A ) = ( G |` A ) )

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
    wss
    cF
    cA
    cres
    cG
    cA
    cres
    wceq
    bnj1503.1
    bnj1503.2
    bnj1503.3
    cA
    cF
    cG
    fun2ssres
    syl3anc
end
