include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cop.mm"
include "cpr.mm"
include "ccnv.mm"
include "csn.mm"
include "cun.mm"
include "wfun.mm"
include "ctp.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "funcnvpr.mm"
include "syl2an3an.mm"
include "funcnvsn.mm"
include "a1i.mm"
include "crn.mm"
include "df-rn.mm"
include "rnpropg.mm"
include "syl5eqr.mm"
include "3adant3.mm"
include "rnsnopg.mm"
include "3ad2ant3.mm"
include "ineq12d.mm"
include "disjprsn.mm"
include "3adant1.mm"
include "sylan9eq.mm"
include "funun.mm"
include "syl21anc.mm"
include "df-tp.mm"
include "cnveqi.mm"
include "cnvun.mm"
include "eqtri.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funcnvtp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( ( A e. U /\ C e. V /\ E e. W ) /\ ( B =/= D /\ B =/= F /\ D =/= F ) ) -> Fun `' { <. A , B >. , <. C , D >. , <. E , F >. } )

  proof
    cA
    cU
    wcel
    #
    cC
    cV
    wcel
    #
    cE
    cW
    wcel
    #
    w3a
    #
    cB
    cD
    wne
    #
    cB
    cF
    wne
    #
    cD
    cF
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cpr
    #
    ccnv
    #
    cE
    cF
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
    @9
    @10
    @13
    ctp
    #
    ccnv
    #
    wfun
    @8
    @12
    wfun
    #
    @15
    wfun
    #
    @12
    cdm
    #
    @15
    cdm
    #
    cin
    #
    c0
    wceq
    @17
    @3
    @0
    @1
    @7
    @4
    @20
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @4
    @5
    @6
    simp1
    cA
    cB
    cC
    cD
    cU
    cV
    funcnvpr
    syl2an3an
    @21
    @8
    cE
    cF
    funcnvsn
    a1i
    @3
    @7
    @24
    cB
    cD
    cpr
    #
    cF
    csn
    #
    cin
    #
    c0
    @3
    @22
    @25
    @23
    @26
    @0
    @1
    @22
    @25
    wceq
    @2
    @0
    @1
    wa
    @22
    @11
    crn
    @25
    @11
    df-rn
    cA
    cC
    cB
    cD
    cU
    cV
    rnpropg
    syl5eqr
    3adant3
    @2
    @0
    @23
    @26
    wceq
    @1
    @2
    @23
    @14
    crn
    @26
    @14
    df-rn
    cE
    cF
    cW
    rnsnopg
    syl5eqr
    3ad2ant3
    ineq12d
    @5
    @6
    @27
    c0
    wceq
    @4
    cB
    cD
    cF
    disjprsn
    3adant1
    sylan9eq
    @12
    @15
    funun
    syl21anc
    @19
    @16
    @19
    @11
    @14
    cun
    #
    ccnv
    @16
    @18
    @28
    @9
    @10
    @13
    df-tp
    cnveqi
    @11
    @14
    cnvun
    eqtri
    funeqi
    sylibr
end
