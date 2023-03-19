include "cnq.mm"
include "wcel.mm"
include "crq.mm"
include "cfv.mm"
include "wceq.mm"
include "cmq.mm"
include "co.mm"
include "c1q.mm"
include "eqid.mm"
include "recmulnq.mm"
include "mpbii.mm"

theorem recidnq
  let cA: class A


  assert |- ( A e. Q. -> ( A .Q ( *Q ` A ) ) = 1Q )

  proof
    cA
    cnq
    wcel
    cA
    crq
    cfv
    #
    @0
    wceq
    cA
    @0
    cmq
    co
    c1q
    wceq
    @0
    eqid
    cA
    @0
    recmulnq
    mpbii
end
