include "wf1.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "df-f1.mm"
include "nff.mm"
include "nfcnv.mm"
include "nffun.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nff1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume nff1.1: |- F/_ x F
  assume nff1.2: |- F/_ x A
  assume nff1.3: |- F/_ x B


  assert |- F/ x F : A -1-1-> B

  proof
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    #
    cF
    ccnv
    #
    wfun
    #
    wa
    vx
    cA
    cB
    cF
    df-f1
    @0
    @2
    vx
    vx
    cA
    cB
    cF
    nff1.1
    nff1.2
    nff1.3
    nff
    vx
    @1
    vx
    cF
    nff1.1
    nfcnv
    nffun
    nfan
    nfxfr
end
