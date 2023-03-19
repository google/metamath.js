include "chli.mm"
include "wbr.mm"
include "cfv.mm"
include "cdm.mm"
include "chil.mm"
include "wf.mm"
include "wfun.mm"
include "wceq.mm"
include "wi.mm"
include "hlimf.mm"
include "ffun.mm"
include "funbrfv.mm"
include "mp2b.mm"
include "sylan9req.mm"

theorem hlimuni
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F ~~>v A /\ F ~~>v B ) -> A = B )

  proof
    cF
    cA
    chli
    wbr
    #
    cF
    cB
    chli
    wbr
    #
    cA
    cF
    chli
    cfv
    #
    cB
    chli
    cdm
    #
    chil
    chli
    wf
    #
    chli
    wfun
    #
    @0
    @2
    cA
    wceq
    wi
    hlimf
    @3
    chil
    chli
    ffun
    #
    cF
    cA
    chli
    funbrfv
    mp2b
    @4
    @5
    @1
    @2
    cB
    wceq
    wi
    hlimf
    @6
    cF
    cB
    chli
    funbrfv
    mp2b
    sylan9req
end
