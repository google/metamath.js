include "wceq.mm"
include "ctrpred.mm"
include "trpredeq1.mm"
include "syl.mm"

theorem trpredeq1d
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cX: class X
  assume trpredeq1d.1: |- ( ph -> R = S )


  assert |- ( ph -> TrPred ( R , A , X ) = TrPred ( S , A , X ) )

  proof
    wph
    cR
    cS
    wceq
    cA
    cR
    cX
    ctrpred
    cA
    cS
    cX
    ctrpred
    wceq
    trpredeq1d.1
    cA
    cR
    cS
    cX
    trpredeq1
    syl
end
