include "cv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "cat.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "cch.mm"
include "cdmd.mm"
include "wbr.mm"
include "wcel.mm"
include "chjcomi.mm"
include "sseq2i.mm"
include "anbi2i.mm"
include "ssin.mm"
include "bitri.mm"
include "weq.mm"
include "mdsymlem5.mm"
include "sseq1.mm"
include "chincl.mm"
include "mpan2.mm"
include "chub2.mm"
include "sylancr.mm"
include "sstr2.mm"
include "syl5.mm"
include "syl6bi.mm"
include "impd.mm"
include "a1i.mm"
include "com13.mm"
include "adantrr.mm"
include "ad2ant2r.mm"
include "adantll.mm"
include "com12.mm"
include "expd.mm"
include "pm2.61d2.mm"
include "rexlimivv.mm"
include "imim2d.mm"
include "com34.mm"
include "imp4b.mm"
include "syl5bir.mm"
include "ex.mm"
include "ralimdva.mm"
include "wb.mm"
include "chjcli.mm"
include "chjcl.mm"
include "sylancl.mm"
include "chrelat3.mm"
include "syl2anc.mm"
include "adantr.mm"
include "sylibrd.mm"
include "com3r.mm"
include "ralrimiv.mm"
include "dmdbr2.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem mdsymlem6
  let cA: class A
  let cB: class B
  let cC: class C
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vc: setvar c
  assume mdsymlem1.1: |- A e. CH
  assume mdsymlem1.2: |- B e. CH
  assume mdsymlem1.3: |- C = ( A vH p )

  disjoint q r
  disjoint C q
  disjoint C r
  disjoint p q
  disjoint p r
  disjoint A p
  disjoint A q
  disjoint A r
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint A c
  disjoint B c
  assert |- ( A. p e. HAtoms ( p C_ ( A vH B ) -> E. q e. HAtoms E. r e. HAtoms ( p C_ ( q vH r ) /\ ( q C_ A /\ r C_ B ) ) ) -> B MH* A )

  proof
    vp
    cv
    #
    cA
    cB
    chj
    co
    #
    wss
    #
    @0
    vq
    cv
    #
    vr
    cv
    #
    chj
    co
    wss
    #
    @3
    cA
    wss
    #
    @4
    cB
    wss
    #
    wa
    #
    wa
    #
    vr
    cat
    wrex
    vq
    cat
    wrex
    #
    wi
    #
    vp
    cat
    wral
    #
    cA
    vc
    cv
    #
    wss
    #
    @13
    cB
    cA
    chj
    co
    #
    cin
    #
    @13
    cB
    cin
    #
    cA
    chj
    co
    #
    wss
    #
    wi
    #
    vc
    cch
    wral
    #
    cB
    cA
    cdmd
    wbr
    #
    @12
    @20
    vc
    cch
    @13
    cch
    wcel
    #
    @14
    @12
    @19
    @23
    @14
    @12
    @19
    wi
    @23
    @14
    wa
    #
    @12
    @0
    @16
    wss
    #
    @0
    @18
    wss
    #
    wi
    #
    vp
    cat
    wral
    #
    @19
    @24
    @11
    @27
    vp
    cat
    @24
    @0
    cat
    wcel
    #
    wa
    #
    @11
    @27
    @25
    @0
    @13
    wss
    #
    @2
    wa
    #
    @30
    @11
    wa
    @26
    @32
    @31
    @0
    @15
    wss
    #
    wa
    @25
    @2
    @33
    @31
    @1
    @15
    @0
    cA
    cB
    mdsymlem1.1
    mdsymlem1.2
    chjcomi
    sseq2i
    anbi2i
    @0
    @13
    @15
    ssin
    bitri
    @30
    @11
    @31
    @2
    @26
    @30
    @11
    @2
    @31
    @26
    @30
    @10
    @31
    @26
    wi
    #
    @2
    @10
    @30
    @34
    @9
    @30
    @34
    wi
    #
    vq
    vr
    cat
    cat
    @3
    cat
    wcel
    @4
    cat
    wcel
    wa
    vq
    vp
    weq
    #
    @9
    @35
    wi
    cA
    cB
    cC
    vr
    vq
    vp
    vc
    mdsymlem1.1
    mdsymlem1.2
    mdsymlem1.3
    mdsymlem5
    @36
    @9
    @30
    @34
    @9
    @30
    wa
    @36
    @34
    @8
    @30
    @36
    @34
    wi
    #
    @5
    @6
    @24
    @37
    @7
    @29
    @6
    @23
    @37
    @14
    @31
    @36
    @6
    @23
    wa
    #
    @26
    @36
    @38
    @26
    wi
    wi
    @31
    @36
    @6
    @23
    @26
    @36
    @6
    @0
    cA
    wss
    #
    @23
    @26
    wi
    @3
    @0
    cA
    sseq1
    @23
    cA
    @18
    wss
    #
    @39
    @26
    @23
    cA
    cch
    wcel
    #
    @17
    cch
    wcel
    #
    @40
    mdsymlem1.1
    @23
    cB
    cch
    wcel
    #
    @42
    mdsymlem1.2
    @13
    cB
    chincl
    mpan2
    #
    cA
    @17
    chub2
    sylancr
    @0
    cA
    @18
    sstr2
    syl5
    syl6bi
    impd
    a1i
    com13
    adantrr
    ad2ant2r
    adantll
    com12
    expd
    pm2.61d2
    rexlimivv
    com12
    imim2d
    com34
    imp4b
    syl5bir
    ex
    ralimdva
    @23
    @19
    @28
    wb
    #
    @14
    @23
    @16
    cch
    wcel
    #
    @18
    cch
    wcel
    #
    @45
    @23
    @15
    cch
    wcel
    @46
    cB
    cA
    mdsymlem1.2
    mdsymlem1.1
    chjcli
    @13
    @15
    chincl
    mpan2
    @23
    @42
    @41
    @47
    @44
    mdsymlem1.1
    @17
    cA
    chjcl
    sylancl
    vp
    @16
    @18
    chrelat3
    syl2anc
    adantr
    sylibrd
    ex
    com3r
    ralrimiv
    @43
    @41
    @22
    @21
    wb
    mdsymlem1.2
    mdsymlem1.1
    vc
    cB
    cA
    dmdbr2
    mp2an
    sylibr
end
