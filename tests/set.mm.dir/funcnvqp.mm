include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "cpr.mm"
include "ccnv.mm"
include "cun.mm"
include "wfun.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "funcnvpr.mm"
include "3expa.mm"
include "3ad2antr1.mm"
include "ad2ant2r.mm"
include "3adantr2.mm"
include "ad2ant2l.mm"
include "crn.mm"
include "df-rn.mm"
include "rnpropg.mm"
include "syl5eqr.mm"
include "ineqan12d.mm"
include "disjpr2.mm"
include "an4s.mm"
include "3adantl1.mm"
include "3adant3.mm"
include "sylan9eq.mm"
include "funun.mm"
include "syl21anc.mm"
include "cnvun.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funcnvqp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W


  assert |- ( ( ( ( A e. U /\ C e. V ) /\ ( E e. W /\ G e. T ) ) /\ ( ( B =/= D /\ B =/= F /\ B =/= H ) /\ ( D =/= F /\ D =/= H ) /\ F =/= H ) ) -> Fun `' ( { <. A , B >. , <. C , D >. } u. { <. E , F >. , <. G , H >. } ) )

  proof
    cA
    cU
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    cE
    cW
    wcel
    #
    cG
    cT
    wcel
    #
    wa
    #
    wa
    #
    cB
    cD
    wne
    #
    cB
    cF
    wne
    #
    cB
    cH
    wne
    #
    w3a
    #
    cD
    cF
    wne
    #
    cD
    cH
    wne
    #
    wa
    #
    cF
    cH
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cop
    cC
    cD
    cop
    cpr
    #
    ccnv
    #
    cE
    cF
    cop
    cG
    cH
    cop
    cpr
    #
    ccnv
    #
    cun
    #
    wfun
    #
    @17
    @19
    cun
    ccnv
    #
    wfun
    @16
    @18
    wfun
    #
    @20
    wfun
    #
    @18
    cdm
    #
    @20
    cdm
    #
    cin
    #
    c0
    wceq
    @22
    @6
    @10
    @14
    @24
    @13
    @2
    @10
    @24
    @5
    @14
    @2
    @8
    @7
    @24
    @9
    @0
    @1
    @7
    @24
    cA
    cB
    cC
    cD
    cU
    cV
    funcnvpr
    3expa
    3ad2antr1
    ad2ant2r
    3adantr2
    @6
    @10
    @14
    @25
    @13
    @5
    @14
    @25
    @2
    @10
    @3
    @4
    @14
    @25
    cE
    cF
    cG
    cH
    cW
    cT
    funcnvpr
    3expa
    ad2ant2l
    3adantr2
    @6
    @15
    @28
    cB
    cD
    cpr
    #
    cF
    cH
    cpr
    #
    cin
    #
    c0
    @2
    @5
    @26
    @29
    @27
    @30
    @2
    @26
    @17
    crn
    @29
    @17
    df-rn
    cA
    cC
    cB
    cD
    cU
    cV
    rnpropg
    syl5eqr
    @5
    @27
    @19
    crn
    @30
    @19
    df-rn
    cE
    cG
    cF
    cH
    cW
    cT
    rnpropg
    syl5eqr
    ineqan12d
    @10
    @13
    @31
    c0
    wceq
    #
    @14
    @8
    @9
    @13
    @32
    @7
    @8
    @11
    @9
    @12
    @32
    cB
    cD
    cF
    cH
    disjpr2
    an4s
    3adantl1
    3adant3
    sylan9eq
    @18
    @20
    funun
    syl21anc
    @23
    @21
    @17
    @19
    cnvun
    funeqi
    sylibr
end
