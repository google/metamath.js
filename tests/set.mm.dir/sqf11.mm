include "cn.mm"
include "wcel.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cprime.mm"
include "wral.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "cn0.mm"
include "nnnn0.mm"
include "pc11.mm"
include "syl2an.mm"
include "ad2ant2r.mm"
include "eleq1.mm"
include "wn.mm"
include "wo.mm"
include "dfbi3.mm"
include "c1.mm"
include "cle.mm"
include "simpll.mm"
include "adantr.mm"
include "simpllr.mm"
include "simpr.mm"
include "sqfpc.mm"
include "syl3anc.mm"
include "nnle1eq1.mm"
include "syl5ibcom.mm"
include "simprl.mm"
include "simplrr.mm"
include "anim12d.mm"
include "eqtr3.mm"
include "syl6.mm"
include "id.mm"
include "pccl.mm"
include "syl2anr.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "jaod.mm"
include "syl5bi.mm"
include "impbid2.mm"
include "pcelnn.mm"
include "bibi12d.mm"
include "bitrd.mm"
include "ralbidva.mm"

theorem sqf11
  let cA: class A
  let cB: class B
  let vp: setvar p
  let vk: setvar k
  let vn: setvar n
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cP: class P

  disjoint A p
  disjoint B p
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint K p
  disjoint M p
  disjoint M x
  disjoint N p
  disjoint S s
  disjoint S x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P p
  assert |- ( ( ( A e. NN /\ ( mmu ` A ) =/= 0 ) /\ ( B e. NN /\ ( mmu ` B ) =/= 0 ) ) -> ( A = B <-> A. p e. Prime ( p || A <-> p || B ) ) )

  proof
    cA
    cn
    wcel
    #
    cA
    cmu
    cfv
    cc0
    wne
    #
    wa
    #
    cB
    cn
    wcel
    #
    cB
    cmu
    cfv
    cc0
    wne
    #
    wa
    #
    wa
    #
    cA
    cB
    wceq
    #
    vp
    cv
    #
    cA
    cpc
    co
    #
    @8
    cB
    cpc
    co
    #
    wceq
    #
    vp
    cprime
    wral
    #
    @8
    cA
    cdvds
    wbr
    #
    @8
    cB
    cdvds
    wbr
    #
    wb
    #
    vp
    cprime
    wral
    @0
    @3
    @7
    @12
    wb
    #
    @1
    @4
    @0
    cA
    cn0
    wcel
    cB
    cn0
    wcel
    @16
    @3
    cA
    nnnn0
    cB
    nnnn0
    cA
    cB
    vp
    pc11
    syl2an
    ad2ant2r
    @6
    @11
    @15
    vp
    cprime
    @6
    @8
    cprime
    wcel
    #
    wa
    #
    @11
    @9
    cn
    wcel
    #
    @10
    cn
    wcel
    #
    wb
    #
    @15
    @18
    @11
    @21
    @9
    @10
    cn
    eleq1
    @21
    @19
    @20
    wa
    #
    @19
    wn
    #
    @20
    wn
    #
    wa
    #
    wo
    @18
    @11
    @19
    @20
    dfbi3
    @18
    @22
    @11
    @25
    @18
    @22
    @9
    c1
    wceq
    #
    @10
    c1
    wceq
    #
    wa
    @11
    @18
    @19
    @26
    @20
    @27
    @18
    @9
    c1
    cle
    wbr
    #
    @19
    @26
    @18
    @0
    @1
    @17
    @28
    @6
    @0
    @17
    @0
    @1
    @5
    simpll
    #
    adantr
    @0
    @1
    @5
    @17
    simpllr
    @6
    @17
    simpr
    #
    cA
    @8
    sqfpc
    syl3anc
    @9
    nnle1eq1
    syl5ibcom
    @18
    @10
    c1
    cle
    wbr
    #
    @20
    @27
    @18
    @3
    @4
    @17
    @31
    @6
    @3
    @17
    @2
    @3
    @4
    simprl
    #
    adantr
    @2
    @3
    @4
    @17
    simplrr
    @30
    cB
    @8
    sqfpc
    syl3anc
    @10
    nnle1eq1
    syl5ibcom
    anim12d
    @9
    @10
    c1
    eqtr3
    syl6
    @18
    @25
    @9
    cc0
    wceq
    #
    @10
    cc0
    wceq
    #
    wa
    @11
    @18
    @23
    @33
    @24
    @34
    @18
    @19
    @33
    @18
    @9
    cn0
    wcel
    #
    @19
    @33
    wo
    @17
    @17
    @0
    @35
    @6
    @17
    id
    #
    @29
    @8
    cA
    pccl
    syl2anr
    @9
    elnn0
    sylib
    ord
    @18
    @20
    @34
    @18
    @10
    cn0
    wcel
    #
    @20
    @34
    wo
    @17
    @17
    @3
    @37
    @6
    @36
    @32
    @8
    cB
    pccl
    syl2anr
    @10
    elnn0
    sylib
    ord
    anim12d
    @9
    @10
    cc0
    eqtr3
    syl6
    jaod
    syl5bi
    impbid2
    @18
    @19
    @13
    @20
    @14
    @17
    @17
    @0
    @19
    @13
    wb
    @6
    @36
    @29
    @8
    cA
    pcelnn
    syl2anr
    @17
    @17
    @3
    @20
    @14
    wb
    @6
    @36
    @32
    @8
    cB
    pcelnn
    syl2anr
    bibi12d
    bitrd
    ralbidva
    bitrd
end
