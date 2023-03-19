include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "cr.mm"
include "nnre.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "adantr.mm"
include "cn0.mm"
include "nnnn0.mm"
include "cfa.mm"
include "cfv.mm"
include "caddc.mm"
include "cz.mm"
include "facndiv.mm"
include "oveq1i.mm"
include "nnz.mm"
include "syl5eqelr.mm"
include "nsyl.mm"
include "sylanl1.mm"
include "expr.mm"
include "sylbird.mm"
include "con4d.mm"
include "expimpd.mm"
include "adantrd.mm"
include "w3a.mm"
include "cc.mm"
include "faccl.mm"
include "syl.mm"
include "peano2nnd.mm"
include "syl5eqel.mm"
include "nncnd.mm"
include "nndivtr.mm"
include "ex.mm"
include "3com13.mm"
include "3expa.mm"
include "adantrl.mm"
include "letri3.mm"
include "syl2an.mm"
include "biimprd.mm"
include "exp4b.mm"
include "com3l.mm"
include "imp32.mm"
include "adantll.mm"
include "imim2d.mm"
include "com23.mm"
include "sylan2d.mm"
include "exp4d.mm"
include "com24.mm"
include "exp32.mm"
include "imp31.mm"
include "com14.mm"
include "3imp.mm"
include "ralimdva.mm"
include "adantld.mm"
include "impd.mm"
include "prime.mm"
include "adantl.mm"
include "sylibrd.mm"
include "jcad.mm"

theorem infpnlem1
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  assume infpnlem.1: |- K = ( ( ! ` N ) + 1 )

  disjoint N j
  disjoint M j
  disjoint K j
  disjoint j k
  disjoint N k
  disjoint K k
  assert |- ( ( N e. NN /\ M e. NN ) -> ( ( ( 1 < M /\ ( K / M ) e. NN ) /\ A. j e. NN ( ( 1 < j /\ ( K / j ) e. NN ) -> M <_ j ) ) -> ( N < M /\ A. j e. NN ( ( M / j ) e. NN -> ( j = 1 \/ j = M ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cM
    cn
    wcel
    #
    wa
    #
    c1
    cM
    clt
    wbr
    #
    cK
    cM
    cdiv
    co
    #
    cn
    wcel
    #
    wa
    #
    c1
    vj
    cv
    #
    clt
    wbr
    #
    cK
    @7
    cdiv
    co
    cn
    wcel
    #
    wa
    #
    cM
    @7
    cle
    wbr
    #
    wi
    #
    vj
    cn
    wral
    #
    wa
    #
    cN
    cM
    clt
    wbr
    #
    cM
    @7
    cdiv
    co
    cn
    wcel
    #
    @7
    c1
    wceq
    @7
    cM
    wceq
    #
    wo
    wi
    vj
    cn
    wral
    #
    @2
    @6
    @15
    @13
    @2
    @3
    @5
    @15
    @2
    @3
    wa
    #
    @15
    @5
    @19
    @15
    wn
    #
    cM
    cN
    cle
    wbr
    #
    @5
    wn
    #
    @2
    @21
    @20
    wb
    #
    @3
    @1
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    @23
    @0
    cM
    nnre
    #
    cN
    nnre
    cM
    cN
    lenlt
    syl2anr
    adantr
    @2
    @3
    @21
    @22
    @0
    cN
    cn0
    wcel
    #
    @1
    @3
    @21
    wa
    #
    @22
    cN
    nnnn0
    #
    @26
    @1
    wa
    @27
    wa
    cN
    cfa
    cfv
    #
    c1
    caddc
    co
    #
    cM
    cdiv
    co
    #
    cz
    wcel
    @5
    cN
    cM
    facndiv
    @5
    @31
    @4
    cz
    cK
    @30
    cM
    cdiv
    infpnlem.1
    oveq1i
    @4
    nnz
    syl5eqelr
    nsyl
    sylanl1
    expr
    sylbird
    con4d
    expimpd
    adantrd
    @2
    @14
    @8
    @7
    cM
    cle
    wbr
    #
    @16
    w3a
    #
    @17
    wi
    #
    vj
    cn
    wral
    #
    @18
    @2
    @6
    @13
    @35
    @2
    @5
    @13
    @35
    wi
    #
    @3
    @2
    @5
    @36
    @2
    @5
    wa
    #
    @12
    @34
    vj
    cn
    @33
    @37
    @7
    cn
    wcel
    #
    wa
    #
    @12
    @17
    @8
    @32
    @16
    @39
    @12
    @17
    wi
    #
    wi
    @39
    @32
    @16
    @8
    @40
    @2
    @5
    @38
    @32
    @16
    @8
    @40
    wi
    wi
    #
    wi
    @2
    @32
    @38
    @5
    @41
    @2
    @32
    @38
    @5
    @41
    wi
    @2
    @32
    @38
    wa
    #
    wa
    #
    @8
    @16
    @5
    @40
    @43
    @8
    @16
    @5
    @40
    @43
    @16
    @5
    wa
    #
    @9
    @8
    @40
    @2
    @38
    @44
    @9
    wi
    #
    @32
    @0
    cK
    cc
    wcel
    #
    @1
    @38
    @45
    @0
    cK
    @0
    cK
    @30
    cn
    infpnlem.1
    @0
    @29
    @0
    @26
    @29
    cn
    wcel
    @28
    cN
    faccl
    syl
    peano2nnd
    syl5eqel
    nncnd
    @46
    @1
    @38
    @45
    @38
    @1
    @46
    @45
    @38
    @1
    @46
    w3a
    @44
    @9
    @7
    cM
    cK
    nndivtr
    ex
    3com13
    3expa
    sylanl1
    adantrl
    @43
    @12
    @10
    @17
    @43
    @11
    @17
    @10
    @1
    @42
    @11
    @17
    wi
    #
    @0
    @1
    @32
    @38
    @47
    @38
    @1
    @32
    @47
    @38
    @1
    @32
    @11
    @17
    @38
    @1
    wa
    @17
    @32
    @11
    wa
    #
    @38
    @7
    cr
    wcel
    @24
    @17
    @48
    wb
    @1
    @7
    nnre
    @25
    @7
    cM
    letri3
    syl2an
    biimprd
    exp4b
    com3l
    imp32
    adantll
    imim2d
    com23
    sylan2d
    exp4d
    com24
    exp32
    com24
    imp31
    com14
    3imp
    com3l
    ralimdva
    ex
    adantld
    impd
    @1
    @18
    @35
    wb
    @0
    vj
    cM
    prime
    adantl
    sylibrd
    jcad
end
