include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cpc.mm"
include "co.mm"
include "cneg.mm"
include "wi.mm"
include "oveq2.mm"
include "a1i.mm"
include "pcneg.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "cr.mm"
include "qre.mm"
include "adantl.mm"
include "absord.mm"
include "mpjaod.mm"

theorem pcabs
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. QQ ) -> ( P pCnt ( abs ` A ) ) = ( P pCnt A ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cq
    wcel
    #
    wa
    #
    cA
    cabs
    cfv
    #
    cA
    wceq
    #
    cP
    @3
    cpc
    co
    #
    cP
    cA
    cpc
    co
    #
    wceq
    #
    @3
    cA
    cneg
    #
    wceq
    #
    @4
    @7
    wi
    @2
    @3
    cA
    cP
    cpc
    oveq2
    a1i
    @2
    @7
    @9
    cP
    @8
    cpc
    co
    #
    @6
    wceq
    cA
    cP
    pcneg
    @9
    @5
    @10
    @6
    @3
    @8
    cP
    cpc
    oveq2
    eqeq1d
    syl5ibrcom
    @2
    cA
    @1
    cA
    cr
    wcel
    @0
    cA
    qre
    adantl
    absord
    mpjaod
end
