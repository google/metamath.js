include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "cun.mm"
include "wfun.mm"
include "cpr.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "funcnvsn.mm"
include "pm3.2i.mm"
include "crn.mm"
include "df-rn.mm"
include "rnsnopg.mm"
include "syl5eqr.mm"
include "ineqan12d.mm"
include "3adant3.mm"
include "disjsn2.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"
include "funun.mm"
include "sylancr.mm"
include "df-pr.mm"
include "cnveqi.mm"
include "cnvun.mm"
include "eqtri.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funcnvpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cV: class V


  assert |- ( ( A e. U /\ C e. V /\ B =/= D ) -> Fun `' { <. A , B >. , <. C , D >. } )

  proof
    cA
    cU
    wcel
    #
    cC
    cV
    wcel
    #
    cB
    cD
    wne
    #
    w3a
    #
    cA
    cB
    cop
    #
    csn
    #
    ccnv
    #
    cC
    cD
    cop
    #
    csn
    #
    ccnv
    #
    cun
    #
    wfun
    #
    @4
    @7
    cpr
    #
    ccnv
    #
    wfun
    @3
    @6
    wfun
    #
    @9
    wfun
    #
    wa
    @6
    cdm
    #
    @9
    cdm
    #
    cin
    #
    c0
    wceq
    @11
    @14
    @15
    cA
    cB
    funcnvsn
    cC
    cD
    funcnvsn
    pm3.2i
    @3
    @18
    cB
    csn
    #
    cD
    csn
    #
    cin
    #
    c0
    @0
    @1
    @18
    @21
    wceq
    @2
    @0
    @1
    @16
    @19
    @17
    @20
    @0
    @16
    @5
    crn
    @19
    @5
    df-rn
    cA
    cB
    cU
    rnsnopg
    syl5eqr
    @1
    @17
    @8
    crn
    @20
    @8
    df-rn
    cC
    cD
    cV
    rnsnopg
    syl5eqr
    ineqan12d
    3adant3
    @2
    @0
    @21
    c0
    wceq
    @1
    cB
    cD
    disjsn2
    3ad2ant3
    eqtrd
    @6
    @9
    funun
    sylancr
    @13
    @10
    @13
    @5
    @8
    cun
    #
    ccnv
    @10
    @12
    @22
    @4
    @7
    df-pr
    cnveqi
    @5
    @8
    cnvun
    eqtri
    funeqi
    sylibr
end
