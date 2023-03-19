include "cv.mm"
include "crq.mm"
include "cfv.mm"
include "wceq.mm"
include "cnq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "cmq.mm"
include "co.mm"
include "c1q.mm"
include "mulcomnq.mm"
include "recidnq.mm"
include "syl5eq.mm"
include "wb.mm"
include "recclnq.mm"
include "recmulnq.mm"
include "syl.mm"
include "mpbird.mm"
include "vtoclga.mm"

theorem recrecnq
  let cA: class A
  let vx: setvar x


  assert |- ( A e. Q. -> ( *Q ` ( *Q ` A ) ) = A )

  proof
    vx
    cv
    #
    crq
    cfv
    #
    crq
    cfv
    #
    @0
    wceq
    #
    cA
    crq
    cfv
    #
    crq
    cfv
    #
    cA
    wceq
    vx
    cA
    cnq
    @0
    cA
    wceq
    #
    @2
    @5
    @0
    cA
    @6
    @1
    @4
    crq
    @0
    cA
    crq
    fveq2
    fveq2d
    @6
    id
    eqeq12d
    @0
    cnq
    wcel
    #
    @3
    @1
    @0
    cmq
    co
    #
    c1q
    wceq
    #
    @7
    @8
    @0
    @1
    cmq
    co
    c1q
    @1
    @0
    mulcomnq
    @0
    recidnq
    syl5eq
    @7
    @1
    cnq
    wcel
    @3
    @9
    wb
    @0
    recclnq
    @1
    @0
    recmulnq
    syl
    mpbird
    vtoclga
end
