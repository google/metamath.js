include "cop.mm"
include "wceq.mm"
include "csn.mm"
include "wcel.mm"
include "opi1.mm"
include "id.mm"
include "syl5eleq.mm"
include "cpr.mm"
include "wi.mm"
include "sneqr.mm"
include "a1i.mm"
include "cvv.mm"
include "oprcl.mm"
include "simpld.mm"
include "prid1g.mm"
include "syl.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "elsni.mm"
include "eqcomd.mm"
include "syl6.mm"
include "wo.mm"
include "wa.mm"
include "dfopg.mm"
include "eleqtrd.mm"
include "elpri.mm"
include "mpjaod.mm"

theorem opth1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opth1.1: |- A e. _V
  assume opth1.2: |- B e. _V


  assert |- ( <. A , B >. = <. C , D >. -> A = C )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    wceq
    #
    cA
    csn
    #
    @1
    wcel
    #
    cA
    cC
    wceq
    #
    @2
    @3
    @0
    @1
    cA
    cB
    opth1.1
    opth1.2
    opi1
    @2
    id
    syl5eleq
    @4
    @3
    cC
    csn
    #
    wceq
    #
    @5
    @3
    cC
    cD
    cpr
    #
    wceq
    #
    @7
    @5
    wi
    @4
    cA
    cC
    opth1.1
    sneqr
    a1i
    @4
    @9
    cC
    @3
    wcel
    #
    @5
    @4
    @10
    @9
    cC
    @8
    wcel
    #
    @4
    cC
    cvv
    wcel
    #
    @11
    @4
    @12
    cD
    cvv
    wcel
    #
    cC
    cD
    @3
    oprcl
    #
    simpld
    cC
    cD
    cvv
    prid1g
    syl
    @3
    @8
    cC
    eleq2
    syl5ibrcom
    @10
    cC
    cA
    cC
    cA
    elsni
    eqcomd
    syl6
    @4
    @3
    @6
    @8
    cpr
    #
    wcel
    @7
    @9
    wo
    @4
    @3
    @1
    @15
    @4
    id
    @4
    @12
    @13
    wa
    @1
    @15
    wceq
    @14
    cC
    cD
    cvv
    cvv
    dfopg
    syl
    eleqtrd
    @3
    @6
    @8
    elpri
    syl
    mpjaod
    syl
end
