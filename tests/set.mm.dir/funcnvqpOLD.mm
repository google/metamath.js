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
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "simp11.mm"
include "funcnvpr.mm"
include "syl2an3an.mm"
include "adantl.mm"
include "simp3.mm"
include "crn.mm"
include "df-rn.mm"
include "rnpropg.mm"
include "syl5eqr.mm"
include "ineqan12d.mm"
include "simp2.mm"
include "anim12i.mm"
include "3adant3.mm"
include "disjpr2.mm"
include "syl2anc.mm"
include "sylan9eq.mm"
include "funun.mm"
include "syl21anc.mm"
include "cnvun.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funcnvqpOLD
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
    @0
    @1
    @15
    @7
    @24
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    @7
    @8
    @9
    @13
    @14
    simp11
    cA
    cB
    cC
    cD
    cU
    cV
    funcnvpr
    syl2an3an
    @6
    @3
    @4
    @15
    @14
    @25
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    @10
    @13
    @14
    simp3
    cE
    cF
    cG
    cH
    cW
    cT
    funcnvpr
    syl2an3an
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
    @15
    @8
    @11
    wa
    #
    @9
    @12
    wa
    #
    @31
    c0
    wceq
    @10
    @13
    @32
    @14
    @10
    @8
    @13
    @11
    @7
    @8
    @9
    simp2
    @11
    @12
    simpl
    anim12i
    3adant3
    @10
    @13
    @33
    @14
    @10
    @9
    @13
    @12
    @7
    @8
    @9
    simp3
    @11
    @12
    simpr
    anim12i
    3adant3
    cB
    cD
    cF
    cH
    disjpr2
    syl2anc
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
