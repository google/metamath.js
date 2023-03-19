include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cop.mm"
include "eqid.mm"
include "funopfvb.mm"
include "mpbii.mm"

theorem funfvop
  let cA: class A
  let cF: class F


  assert |- ( ( Fun F /\ A e. dom F ) -> <. A , ( F ` A ) >. e. F )

  proof
    cF
    wfun
    cA
    cF
    cdm
    wcel
    wa
    cA
    cF
    cfv
    #
    @0
    wceq
    cA
    @0
    cop
    cF
    wcel
    @0
    eqid
    cA
    @0
    cF
    funopfvb
    mpbii
end
