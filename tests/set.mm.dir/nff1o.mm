include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "df-f1o.mm"
include "nff1.mm"
include "nffo.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nff1o
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume nff1o.1: |- F/_ x F
  assume nff1o.2: |- F/_ x A
  assume nff1o.3: |- F/_ x B


  assert |- F/ x F : A -1-1-onto-> B

  proof
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cF
    wfo
    #
    wa
    vx
    cA
    cB
    cF
    df-f1o
    @0
    @1
    vx
    vx
    cA
    cB
    cF
    nff1o.1
    nff1o.2
    nff1o.3
    nff1
    vx
    cA
    cB
    cF
    nff1o.1
    nff1o.2
    nff1o.3
    nffo
    nfan
    nfxfr
end
