include "cn.mm"
include "wcel.mm"
include "cvma.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wreu.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "isppw.mm"
include "wb.mm"
include "wral.mm"
include "reu6.mm"
include "wa.mm"
include "cpc.mm"
include "equid.mm"
include "breq1.mm"
include "equequ1.mm"
include "bibi12d.mm"
include "rspcva.mm"
include "adantll.mm"
include "mpbiri.mm"
include "simplr.mm"
include "simpll.mm"
include "pcelnn.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "simpr.mm"
include "oveq1d.mm"
include "cz.mm"
include "simpllr.mm"
include "cn0.mm"
include "pccl.mm"
include "ancoms.mm"
include "ad2antrr.mm"
include "nn0zd.mm"
include "pcid.mm"
include "eqtr4d.mm"
include "wn.mm"
include "simprr.mm"
include "notbid.mm"
include "biimpar.mm"
include "simplrl.mm"
include "simplll.mm"
include "pceq0.mm"
include "wi.mm"
include "simprl.mm"
include "adantr.mm"
include "prmdvdsexpr.mm"
include "syl3anc.mm"
include "con3dimp.mm"
include "prmnn.mm"
include "adantl.mm"
include "nnexpcld.mm"
include "pm2.61dan.mm"
include "expr.mm"
include "ralimdva.mm"
include "imp.mm"
include "nnnn0.mm"
include "nnnn0d.mm"
include "pc11.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "prmdvdsexpb.mm"
include "3coml.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "bibi1d.mm"
include "ralbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "rexbidva.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem isppw2
  let cA: class A
  let vk: setvar k
  let vp: setvar p
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
  let cB: class B
  let cP: class P

  disjoint k p
  disjoint A k
  disjoint A p
  disjoint k n
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint k z
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
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P p
  assert |- ( A e. NN -> ( ( Lam ` A ) =/= 0 <-> E. p e. Prime E. k e. NN A = ( p ^ k ) ) )

  proof
    cA
    cn
    wcel
    #
    cA
    cvma
    cfv
    cc0
    wne
    vq
    cv
    #
    cA
    cdvds
    wbr
    #
    vq
    cprime
    wreu
    #
    cA
    vp
    cv
    #
    vk
    cv
    #
    cexp
    co
    #
    wceq
    #
    vk
    cn
    wrex
    #
    vp
    cprime
    wrex
    #
    cA
    vq
    isppw
    @3
    @2
    @1
    @4
    wceq
    #
    wb
    #
    vq
    cprime
    wral
    #
    vp
    cprime
    wrex
    @0
    @9
    @2
    vq
    vp
    cprime
    reu6
    @0
    @12
    @8
    vp
    cprime
    @0
    @4
    cprime
    wcel
    #
    wa
    #
    @12
    @8
    @14
    @12
    @8
    @14
    @12
    wa
    #
    @4
    cA
    cpc
    co
    #
    cn
    wcel
    #
    cA
    @4
    @16
    cexp
    co
    #
    wceq
    #
    @8
    @15
    @17
    @4
    cA
    cdvds
    wbr
    #
    @15
    @20
    @4
    @4
    wceq
    #
    vp
    equid
    @13
    @12
    @20
    @21
    wb
    #
    @0
    @11
    @22
    vq
    @4
    cprime
    @10
    @2
    @20
    @10
    @21
    @1
    @4
    cA
    cdvds
    breq1
    vq
    vp
    vp
    equequ1
    bibi12d
    rspcva
    adantll
    mpbiri
    @15
    @13
    @0
    @17
    @20
    wb
    @0
    @13
    @12
    simplr
    @0
    @13
    @12
    simpll
    @4
    cA
    pcelnn
    syl2anc
    mpbird
    @15
    @19
    @1
    cA
    cpc
    co
    #
    @1
    @18
    cpc
    co
    #
    wceq
    #
    vq
    cprime
    wral
    #
    @14
    @12
    @26
    @14
    @11
    @25
    vq
    cprime
    @14
    @1
    cprime
    wcel
    #
    @11
    @25
    @14
    @27
    @11
    wa
    #
    wa
    #
    @10
    @25
    @29
    @10
    wa
    #
    @23
    @4
    @18
    cpc
    co
    #
    @24
    @30
    @23
    @16
    @31
    @30
    @1
    @4
    cA
    cpc
    @29
    @10
    simpr
    #
    oveq1d
    @30
    @13
    @16
    cz
    wcel
    @31
    @16
    wceq
    @0
    @13
    @28
    @10
    simpllr
    @30
    @16
    @14
    @16
    cn0
    wcel
    #
    @28
    @10
    @13
    @0
    @33
    @4
    cA
    pccl
    ancoms
    #
    ad2antrr
    nn0zd
    @16
    @4
    pcid
    syl2anc
    eqtr4d
    @30
    @1
    @4
    @18
    cpc
    @32
    oveq1d
    eqtr4d
    @29
    @10
    wn
    #
    wa
    #
    @23
    cc0
    @24
    @36
    @23
    cc0
    wceq
    #
    @2
    wn
    #
    @29
    @38
    @35
    @29
    @2
    @10
    @14
    @27
    @11
    simprr
    notbid
    biimpar
    @36
    @27
    @0
    @37
    @38
    wb
    @14
    @27
    @11
    @35
    simplrl
    #
    @0
    @13
    @28
    @35
    simplll
    @1
    cA
    pceq0
    syl2anc
    mpbird
    @36
    @24
    cc0
    wceq
    #
    @1
    @18
    cdvds
    wbr
    #
    wn
    #
    @29
    @41
    @10
    @29
    @27
    @13
    @33
    @41
    @10
    wi
    @14
    @27
    @11
    simprl
    @0
    @13
    @28
    simplr
    @14
    @33
    @28
    @34
    adantr
    @1
    @4
    @16
    prmdvdsexpr
    syl3anc
    con3dimp
    @36
    @27
    @18
    cn
    wcel
    #
    @40
    @42
    wb
    @39
    @14
    @43
    @28
    @35
    @14
    @4
    @16
    @13
    @4
    cn
    wcel
    @0
    @4
    prmnn
    adantl
    @34
    nnexpcld
    #
    ad2antrr
    @1
    @18
    pceq0
    syl2anc
    mpbird
    eqtr4d
    pm2.61dan
    expr
    ralimdva
    imp
    @15
    cA
    cn0
    wcel
    #
    @18
    cn0
    wcel
    @19
    @26
    wb
    @0
    @45
    @13
    @12
    cA
    nnnn0
    ad2antrr
    @15
    @18
    @14
    @43
    @12
    @44
    adantr
    nnnn0d
    cA
    @18
    vq
    pc11
    syl2anc
    mpbird
    @7
    @19
    vk
    @16
    cn
    @5
    @16
    wceq
    @6
    @18
    cA
    @5
    @16
    @4
    cexp
    oveq2
    eqeq2d
    rspcev
    syl2anc
    ex
    @14
    @7
    @12
    vk
    cn
    @14
    @5
    cn
    wcel
    #
    wa
    @12
    @7
    @1
    @6
    cdvds
    wbr
    #
    @10
    wb
    #
    vq
    cprime
    wral
    #
    @13
    @46
    @49
    @0
    @13
    @46
    wa
    @48
    vq
    cprime
    @13
    @46
    @27
    @48
    @27
    @13
    @46
    @48
    @1
    @4
    @5
    prmdvdsexpb
    3coml
    3expa
    ralrimiva
    adantll
    @7
    @11
    @48
    vq
    cprime
    @7
    @2
    @47
    @10
    cA
    @6
    @1
    cdvds
    breq2
    bibi1d
    ralbidv
    syl5ibrcom
    rexlimdva
    impbid
    rexbidva
    syl5bb
    bitrd
end
