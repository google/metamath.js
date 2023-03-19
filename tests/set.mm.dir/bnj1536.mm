include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "fvreseq.mm"
include "syl21anc.mm"
include "mpbird.mm"

theorem bnj1536
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume bnj1536.1: |- ( ph -> F Fn A )
  assume bnj1536.2: |- ( ph -> G Fn A )
  assume bnj1536.3: |- ( ph -> B C_ A )
  assume bnj1536.4: |- ( ph -> A. x e. B ( F ` x ) = ( G ` x ) )

  disjoint B x
  disjoint F x
  disjoint G x
  assert |- ( ph -> ( F |` B ) = ( G |` B ) )

  proof
    wph
    cF
    cB
    cres
    cG
    cB
    cres
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    @1
    cG
    cfv
    wceq
    vx
    cB
    wral
    #
    bnj1536.4
    wph
    cF
    cA
    wfn
    cG
    cA
    wfn
    cB
    cA
    wss
    @0
    @2
    wb
    bnj1536.1
    bnj1536.2
    bnj1536.3
    vx
    cA
    cB
    cF
    cG
    fvreseq
    syl21anc
    mpbird
end
