include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "c1.mm"
include "wb.mm"
include "wne.mm"
include "simpl.mm"
include "gt0ne0.mm"
include "jca.mm"
include "redivcl.mm"
include "3expb.mm"
include "sylan2.mm"
include "adantlr.mm"
include "divgt0.mm"
include "lerec.mm"
include "syl2an.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "adantr.mm"
include "recdiv.mm"
include "breqan12rd.mm"
include "bitrd.mm"

theorem ledivdiv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) ) /\ ( ( C e. RR /\ 0 < C ) /\ ( D e. RR /\ 0 < D ) ) ) -> ( ( A / B ) <_ ( C / D ) <-> ( D / C ) <_ ( B / A ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    wa
    #
    cD
    cr
    wcel
    #
    cc0
    cD
    clt
    wbr
    #
    wa
    #
    wa
    #
    wa
    cA
    cB
    cdiv
    co
    #
    cC
    cD
    cdiv
    co
    #
    cle
    wbr
    #
    c1
    @15
    cdiv
    co
    #
    c1
    @14
    cdiv
    co
    #
    cle
    wbr
    #
    cD
    cC
    cdiv
    co
    #
    cB
    cA
    cdiv
    co
    #
    cle
    wbr
    @6
    @14
    cr
    wcel
    #
    cc0
    @14
    clt
    wbr
    #
    wa
    @15
    cr
    wcel
    #
    cc0
    @15
    clt
    wbr
    #
    wa
    @16
    @19
    wb
    @13
    @6
    @22
    @23
    @0
    @5
    @22
    @1
    @5
    @0
    @3
    cB
    cc0
    wne
    #
    wa
    @22
    @5
    @3
    @26
    @3
    @4
    simpl
    cB
    gt0ne0
    #
    jca
    @0
    @3
    @26
    @22
    cA
    cB
    redivcl
    3expb
    sylan2
    adantlr
    cA
    cB
    divgt0
    jca
    @13
    @24
    @25
    @7
    @12
    @24
    @8
    @12
    @7
    @10
    cD
    cc0
    wne
    #
    wa
    @24
    @12
    @10
    @28
    @10
    @11
    simpl
    cD
    gt0ne0
    #
    jca
    @7
    @10
    @28
    @24
    cC
    cD
    redivcl
    3expb
    sylan2
    adantlr
    cC
    cD
    divgt0
    jca
    @14
    @15
    lerec
    syl2an
    @13
    @6
    @17
    @20
    @18
    @21
    cle
    @9
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    cD
    cc
    wcel
    #
    @28
    wa
    @17
    @20
    wceq
    @12
    @9
    @30
    @31
    @7
    @30
    @8
    cC
    recn
    adantr
    cC
    gt0ne0
    jca
    @12
    @32
    @28
    @10
    @32
    @11
    cD
    recn
    adantr
    @29
    jca
    cC
    cD
    recdiv
    syl2an
    @2
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    cB
    cc
    wcel
    #
    @26
    wa
    @18
    @21
    wceq
    @5
    @2
    @33
    @34
    @0
    @33
    @1
    cA
    recn
    adantr
    cA
    gt0ne0
    jca
    @5
    @35
    @26
    @3
    @35
    @4
    cB
    recn
    adantr
    @27
    jca
    cA
    cB
    recdiv
    syl2an
    breqan12rd
    bitrd
end
