include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "w3a.mm"
include "wa.mm"
include "cwlks.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "eqid.mm"
include "wlkonprop.mm"
include "wi.mm"
include "simp2.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "simp3.mm"
include "adantl.mm"
include "c1.mm"
include "cmin.mm"
include "wlklenvm1.mm"
include "eqtr3.mm"
include "fveq2d.mm"
include "ex.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "com12.mm"
include "imp.mm"
include "simpl3.mm"
include "3eqtrd.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "syl2an.mm"

theorem wlksoneq1eq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H


  assert |- ( ( F ( A ( WalksOn ` G ) B ) P /\ H ( C ( WalksOn ` G ) D ) P ) -> ( A = C /\ B = D ) )

  proof
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    #
    co
    wbr
    cG
    cvv
    wcel
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    cB
    @2
    wcel
    w3a
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    #
    wa
    #
    cF
    cP
    cG
    cwlks
    cfv
    #
    wbr
    #
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    cB
    wceq
    #
    w3a
    #
    w3a
    #
    @1
    cC
    @2
    wcel
    cD
    @2
    wcel
    w3a
    #
    cH
    cvv
    wcel
    @4
    wa
    #
    cH
    cP
    @6
    wbr
    #
    @8
    cC
    wceq
    #
    cH
    chash
    cfv
    #
    cP
    cfv
    #
    cD
    wceq
    #
    w3a
    #
    w3a
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    cH
    cP
    cC
    cD
    @0
    co
    wbr
    cA
    cB
    cP
    cF
    cG
    @2
    @2
    eqid
    #
    wlkonprop
    cC
    cD
    cP
    cH
    cG
    @2
    @27
    wlkonprop
    @14
    @23
    @26
    @13
    @3
    @23
    @26
    wi
    @5
    @23
    @13
    @26
    @22
    @15
    @13
    @26
    wi
    @16
    @22
    @13
    @26
    @22
    @13
    wa
    #
    @24
    @25
    @13
    @22
    cA
    @8
    cC
    @13
    @8
    cA
    @7
    @9
    @12
    simp2
    eqcomd
    @17
    @18
    @21
    simp2
    sylan9eqr
    @28
    cB
    @11
    @20
    cD
    @13
    cB
    @11
    wceq
    @22
    @13
    @11
    cB
    @7
    @9
    @12
    simp3
    eqcomd
    adantl
    @22
    @13
    @11
    @20
    wceq
    #
    @17
    @18
    @13
    @29
    wi
    #
    @21
    @17
    @19
    cP
    chash
    cfv
    c1
    cmin
    co
    #
    wceq
    #
    @30
    cP
    cH
    cG
    wlklenvm1
    @13
    @32
    @29
    @7
    @9
    @32
    @29
    wi
    #
    @12
    @7
    @10
    @31
    wceq
    #
    @33
    cP
    cF
    cG
    wlklenvm1
    @34
    @32
    @29
    @34
    @32
    wa
    @10
    @19
    cP
    @10
    @19
    @31
    eqtr3
    fveq2d
    ex
    syl
    3ad2ant1
    com12
    syl
    3ad2ant1
    imp
    @17
    @18
    @21
    @13
    simpl3
    3eqtrd
    jca
    ex
    3ad2ant3
    com12
    3ad2ant3
    imp
    syl2an
end
