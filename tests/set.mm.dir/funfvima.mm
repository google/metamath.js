include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cima.mm"
include "wi.mm"
include "cres.mm"
include "dmres.mm"
include "elin2.mm"
include "crn.mm"
include "funres.mm"
include "fvelrn.mm"
include "sylan.mm"
include "fvres.mm"
include "eleq1d.mm"
include "df-ima.mm"
include "eleq2i.mm"
include "syl6rbbr.mm"
include "syl5ibrcom.mm"
include "ex.mm"
include "syl5bir.mm"
include "expd.mm"
include "com12.mm"
include "impd.mm"
include "pm2.43b.mm"

theorem funfvima
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ B e. dom F ) -> ( B e. A -> ( F ` B ) e. ( F " A ) ) )

  proof
    cF
    wfun
    #
    cB
    cF
    cdm
    #
    wcel
    #
    wa
    cB
    cA
    wcel
    #
    cB
    cF
    cfv
    #
    cF
    cA
    cima
    #
    wcel
    #
    @3
    @0
    @2
    @3
    @6
    wi
    #
    @0
    @3
    @2
    @7
    wi
    @0
    @3
    @2
    @7
    @3
    @2
    wa
    cB
    cF
    cA
    cres
    #
    cdm
    #
    wcel
    #
    @0
    @7
    cB
    cA
    @1
    @9
    cF
    cA
    dmres
    elin2
    @0
    @10
    @7
    @0
    @10
    wa
    @6
    @3
    cB
    @8
    cfv
    #
    @8
    crn
    #
    wcel
    #
    @0
    @8
    wfun
    @10
    @13
    cA
    cF
    funres
    cB
    @8
    fvelrn
    sylan
    @3
    @13
    @4
    @12
    wcel
    @6
    @3
    @11
    @4
    @12
    cB
    cA
    cF
    fvres
    eleq1d
    @5
    @12
    @4
    cF
    cA
    df-ima
    eleq2i
    syl6rbbr
    syl5ibrcom
    ex
    syl5bir
    expd
    com12
    impd
    pm2.43b
end
