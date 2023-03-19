include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "df-fn.mm"
include "nffun.mm"
include "nfdm.mm"
include "nfeq.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nffn
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume nffn.1: |- F/_ x F
  assume nffn.2: |- F/_ x A


  assert |- F/ x F Fn A

  proof
    cF
    cA
    wfn
    cF
    wfun
    #
    cF
    cdm
    #
    cA
    wceq
    #
    wa
    vx
    cF
    cA
    df-fn
    @0
    @2
    vx
    vx
    cF
    nffn.1
    nffun
    vx
    @1
    cA
    vx
    cF
    nffn.1
    nfdm
    nffn.2
    nfeq
    nfan
    nfxfr
end
