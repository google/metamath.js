include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "ianor.mm"
include "clt.mm"
include "wb.mm"
include "0re.mm"
include "ltnle.mm"
include "mpan.mm"
include "adantr.mm"
include "adantl.mm"
include "orbi12d.mm"
include "wi.mm"
include "ltle.mm"
include "imp.mm"
include "ad2ant2rl.mm"
include "cdiv.mm"
include "remulcl.mm"
include "simprl.mm"
include "simpll.mm"
include "simprr.mm"
include "divge0.mm"
include "syl22anc.mm"
include "cc.mm"
include "recn.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "wne.mm"
include "gt0ne0.mm"
include "divcan3d.mm"
include "breqtrd.mm"
include "jca.mm"
include "expr.mm"
include "simplr.mm"
include "ad2ant2l.mm"
include "divcan4d.mm"
include "jaod.mm"
include "sylbird.mm"
include "syl5bi.mm"
include "orrd.mm"
include "ex.mm"
include "cneg.mm"
include "le0neg1.mm"
include "bi2anan9.mm"
include "renegcl.mm"
include "mulge0.mm"
include "an4s.mm"
include "syl2an.mm"
include "wceq.mm"
include "mul2neg.mm"
include "breq2d.mm"
include "sylibd.mm"
include "sylbid.mm"
include "impbid.mm"

theorem mulge0b
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 <_ ( A x. B ) <-> ( ( A <_ 0 /\ B <_ 0 ) \/ ( 0 <_ A /\ 0 <_ B ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    cB
    cmul
    co
    #
    cle
    wbr
    #
    cA
    cc0
    cle
    wbr
    #
    cB
    cc0
    cle
    wbr
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wo
    #
    @2
    @4
    @11
    @2
    @4
    wa
    #
    @7
    @10
    @7
    wn
    @5
    wn
    #
    @6
    wn
    #
    wo
    #
    @12
    @10
    @5
    @6
    ianor
    @12
    @15
    cc0
    cA
    clt
    wbr
    #
    cc0
    cB
    clt
    wbr
    #
    wo
    #
    @10
    @2
    @18
    @15
    wb
    @4
    @2
    @16
    @13
    @17
    @14
    @0
    @16
    @13
    wb
    #
    @1
    cc0
    cr
    wcel
    #
    @0
    @19
    0re
    cc0
    cA
    ltnle
    mpan
    adantr
    @1
    @17
    @14
    wb
    #
    @0
    @20
    @1
    @21
    0re
    cc0
    cB
    ltnle
    mpan
    adantl
    orbi12d
    adantr
    @12
    @16
    @10
    @17
    @2
    @4
    @16
    @10
    @2
    @4
    @16
    wa
    #
    wa
    #
    @8
    @9
    @0
    @16
    @8
    @1
    @4
    @0
    @16
    @8
    @20
    @0
    @16
    @8
    wi
    0re
    cc0
    cA
    ltle
    mpan
    imp
    ad2ant2rl
    @23
    cc0
    @3
    cA
    cdiv
    co
    #
    cB
    cle
    @23
    @3
    cr
    wcel
    #
    @4
    @0
    @16
    cc0
    @24
    cle
    wbr
    @2
    @25
    @22
    cA
    cB
    remulcl
    #
    adantr
    @2
    @4
    @16
    simprl
    @0
    @1
    @22
    simpll
    @2
    @4
    @16
    simprr
    @3
    cA
    divge0
    syl22anc
    @23
    cB
    cA
    @1
    cB
    cc
    wcel
    #
    @0
    @22
    cB
    recn
    #
    ad2antlr
    @0
    cA
    cc
    wcel
    #
    @1
    @22
    cA
    recn
    #
    ad2antrr
    @0
    @16
    cA
    cc0
    wne
    @1
    @4
    cA
    gt0ne0
    ad2ant2rl
    divcan3d
    breqtrd
    jca
    expr
    @2
    @4
    @17
    @10
    @2
    @4
    @17
    wa
    #
    wa
    #
    @8
    @9
    @32
    cc0
    @3
    cB
    cdiv
    co
    #
    cA
    cle
    @32
    @25
    @4
    @1
    @17
    cc0
    @33
    cle
    wbr
    @2
    @25
    @31
    @26
    adantr
    @2
    @4
    @17
    simprl
    @0
    @1
    @31
    simplr
    @2
    @4
    @17
    simprr
    @3
    cB
    divge0
    syl22anc
    @32
    cA
    cB
    @0
    @29
    @1
    @31
    @30
    ad2antrr
    @1
    @27
    @0
    @31
    @28
    ad2antlr
    @1
    @17
    cB
    cc0
    wne
    @0
    @4
    cB
    gt0ne0
    ad2ant2l
    divcan4d
    breqtrd
    @1
    @17
    @9
    @0
    @4
    @1
    @17
    @9
    @20
    @1
    @17
    @9
    wi
    0re
    cc0
    cB
    ltle
    mpan
    imp
    ad2ant2l
    jca
    expr
    jaod
    sylbird
    syl5bi
    orrd
    ex
    @2
    @7
    @4
    @10
    @2
    @7
    cc0
    cA
    cneg
    #
    cle
    wbr
    #
    cc0
    cB
    cneg
    #
    cle
    wbr
    #
    wa
    #
    @4
    @0
    @5
    @35
    @1
    @6
    @37
    cA
    le0neg1
    cB
    le0neg1
    bi2anan9
    @2
    @38
    cc0
    @34
    @36
    cmul
    co
    #
    cle
    wbr
    #
    @4
    @0
    @34
    cr
    wcel
    #
    @36
    cr
    wcel
    #
    @38
    @40
    wi
    @1
    cA
    renegcl
    cB
    renegcl
    @41
    @42
    wa
    @38
    @40
    @41
    @35
    @42
    @37
    @40
    @34
    @36
    mulge0
    an4s
    ex
    syl2an
    @2
    @39
    @3
    cc0
    cle
    @0
    @29
    @27
    @39
    @3
    wceq
    @1
    @30
    @28
    cA
    cB
    mul2neg
    syl2an
    breq2d
    sylibd
    sylbid
    @2
    @10
    @4
    @0
    @8
    @1
    @9
    @4
    cA
    cB
    mulge0
    an4s
    ex
    jaod
    impbid
end
