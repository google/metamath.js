include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "df-fo.mm"
include "nffn.mm"
include "nfrn.mm"
include "nfeq.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nffo
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume nffo.1: |- F/_ x F
  assume nffo.2: |- F/_ x A
  assume nffo.3: |- F/_ x B


  assert |- F/ x F : A -onto-> B

  proof
    cA
    cB
    cF
    wfo
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wceq
    #
    wa
    vx
    cA
    cB
    cF
    df-fo
    @0
    @2
    vx
    vx
    cA
    cF
    nffo.1
    nffo.2
    nffn
    vx
    @1
    cB
    vx
    cF
    nffo.1
    nfrn
    nffo.3
    nfeq
    nfan
    nfxfr
end
