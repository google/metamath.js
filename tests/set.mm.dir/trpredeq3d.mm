include "wceq.mm"
include "ctrpred.mm"
include "trpredeq3.mm"
include "syl.mm"

theorem trpredeq3d
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  assume trpredeq3d.1: |- ( ph -> X = Y )


  assert |- ( ph -> TrPred ( R , A , X ) = TrPred ( R , A , Y ) )

  proof
    wph
    cX
    cY
    wceq
    cA
    cR
    cX
    ctrpred
    cA
    cR
    cY
    ctrpred
    wceq
    trpredeq3d.1
    cA
    cR
    cX
    cY
    trpredeq3
    syl
end
