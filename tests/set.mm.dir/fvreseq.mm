include "wfn.mm"
include "wa.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wb.mm"
include "fvreseq0.mm"
include "anabsan2.mm"

theorem fvreseq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G

  disjoint B x
  disjoint F x
  disjoint G x
  assert |- ( ( ( F Fn A /\ G Fn A ) /\ B C_ A ) -> ( ( F |` B ) = ( G |` B ) <-> A. x e. B ( F ` x ) = ( G ` x ) ) )

  proof
    cF
    cA
    wfn
    cG
    cA
    wfn
    wa
    cB
    cA
    wss
    cF
    cB
    cres
    cG
    cB
    cres
    wceq
    vx
    cv
    #
    cF
    cfv
    @0
    cG
    cfv
    wceq
    vx
    cB
    wral
    wb
    vx
    cA
    cB
    cA
    cF
    cG
    fvreseq0
    anabsan2
end
