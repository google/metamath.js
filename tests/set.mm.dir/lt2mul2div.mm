include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "adantl.mm"
include "wne.mm"
include "ad2antll.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "gt0ne0.mm"
include "jca.mm"
include "divass.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "adantrrr.mm"
include "adantll.mm"
include "breq2d.mm"
include "wb.mm"
include "simpll.mm"
include "remulcl.mm"
include "adantrr.mm"
include "simplr.mm"
include "ltmuldiv.mm"
include "simpl.mm"
include "redivcl.mm"
include "3expb.mm"
include "sylan2.mm"
include "ancoms.mm"
include "ad2ant2lr.mm"
include "simprr.mm"
include "ltdivmul.mm"
include "3bitr4d.mm"

theorem lt2mul2div
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ ( B e. RR /\ 0 < B ) ) /\ ( C e. RR /\ ( D e. RR /\ 0 < D ) ) ) -> ( ( A x. B ) < ( C x. D ) <-> ( A / D ) < ( C / B ) ) )

  proof
    cA
    cr
    wcel
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
    #
    cA
    cC
    cD
    cmul
    co
    #
    cB
    cdiv
    co
    #
    clt
    wbr
    #
    cA
    cD
    cC
    cB
    cdiv
    co
    #
    cmul
    co
    #
    clt
    wbr
    #
    cA
    cB
    cmul
    co
    @11
    clt
    wbr
    #
    cA
    cD
    cdiv
    co
    @14
    clt
    wbr
    #
    @10
    @12
    @15
    cA
    clt
    @3
    @9
    @12
    @15
    wceq
    #
    @0
    @3
    @5
    @6
    @19
    @7
    @3
    @5
    @6
    wa
    #
    wa
    #
    @12
    cD
    cC
    cmul
    co
    #
    cB
    cdiv
    co
    #
    @15
    @20
    @12
    @23
    wceq
    @3
    @20
    @11
    @22
    cB
    cdiv
    @5
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    @11
    @22
    wceq
    @6
    cC
    recn
    #
    cD
    recn
    #
    cC
    cD
    mulcom
    syl2an
    oveq1d
    adantl
    @21
    @25
    @24
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    @23
    @15
    wceq
    @6
    @25
    @3
    @5
    @27
    ad2antll
    @5
    @24
    @3
    @6
    @26
    ad2antrl
    @3
    @30
    @20
    @3
    @28
    @29
    @1
    @28
    @2
    cB
    recn
    adantr
    cB
    gt0ne0
    #
    jca
    adantr
    cD
    cC
    cB
    divass
    syl3anc
    eqtrd
    adantrrr
    adantll
    breq2d
    @10
    @0
    @11
    cr
    wcel
    #
    @3
    @17
    @13
    wb
    @0
    @3
    @9
    simpll
    #
    @9
    @32
    @4
    @5
    @6
    @32
    @7
    cC
    cD
    remulcl
    adantrr
    adantl
    @0
    @3
    @9
    simplr
    cA
    @11
    cB
    ltmuldiv
    syl3anc
    @10
    @0
    @14
    cr
    wcel
    #
    @8
    @18
    @16
    wb
    @33
    @3
    @5
    @34
    @0
    @8
    @5
    @3
    @34
    @3
    @5
    @1
    @29
    wa
    @34
    @3
    @1
    @29
    @1
    @2
    simpl
    @31
    jca
    @5
    @1
    @29
    @34
    cC
    cB
    redivcl
    3expb
    sylan2
    ancoms
    ad2ant2lr
    @4
    @5
    @8
    simprr
    cA
    @14
    cD
    ltdivmul
    syl3anc
    3bitr4d
end
