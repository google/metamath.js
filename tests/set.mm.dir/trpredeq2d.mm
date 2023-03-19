include "wceq.mm"
include "ctrpred.mm"
include "trpredeq2.mm"
include "syl.mm"

theorem trpredeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume trpredeq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> TrPred ( R , A , X ) = TrPred ( R , B , X ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cR
    cX
    ctrpred
    cB
    cR
    cX
    ctrpred
    wceq
    trpredeq2d.1
    cA
    cB
    cR
    cX
    trpredeq2
    syl
end
