include "wcel.mm"
include "cpr.mm"
include "csn.mm"
include "c1o.mm"
include "cen.mm"
include "dfsn2.mm"
include "ensn1g.mm"
include "syl5eqbrr.mm"

theorem enpr1g
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> { A , A } ~~ 1o )

  proof
    cA
    cV
    wcel
    cA
    cA
    cpr
    cA
    csn
    c1o
    cen
    cA
    dfsn2
    cA
    cV
    ensn1g
    syl5eqbrr
end
