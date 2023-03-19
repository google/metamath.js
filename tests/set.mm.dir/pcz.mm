include "cq.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cprime.mm"
include "wral.mm"
include "pcge0.mm"
include "ancoms.mm"
include "ralrimiva.mm"
include "cdiv.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "elq.mm"
include "wa.mm"
include "cdvds.mm"
include "nnz.mm"
include "dvds0.mm"
include "syl.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "breqtrrd.mm"
include "a1d.mm"
include "wne.mm"
include "cmin.mm"
include "simplll.mm"
include "simplr.mm"
include "simpllr.mm"
include "pcdiv.mm"
include "syl121anc.mm"
include "breq2d.mm"
include "cn0.mm"
include "pczcl.mm"
include "syl12anc.mm"
include "nn0red.mm"
include "pccld.mm"
include "subge0d.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "wb.mm"
include "id.mm"
include "pc2dvds.mm"
include "syl2anr.mm"
include "adantr.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "pm2.61dane.mm"
include "adantl.mm"
include "nnne0.mm"
include "simpl.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "sylibd.mm"
include "oveq2.mm"
include "ralbidv.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "impbid2.mm"

theorem pcz
  let cA: class A
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let cB: class B

  disjoint A p
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B p
  assert |- ( A e. QQ -> ( A e. ZZ <-> A. p e. Prime 0 <_ ( p pCnt A ) ) )

  proof
    cA
    cq
    wcel
    #
    cA
    cz
    wcel
    #
    cc0
    vp
    cv
    #
    cA
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @1
    @4
    vp
    cprime
    @2
    cprime
    wcel
    #
    @1
    @4
    @2
    cA
    pcge0
    ancoms
    ralrimiva
    @0
    cA
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    @5
    @1
    wi
    #
    vx
    vy
    cA
    elq
    @10
    @11
    vx
    vy
    cz
    cn
    @7
    cz
    wcel
    #
    @8
    cn
    wcel
    #
    wa
    #
    @11
    @10
    cc0
    @2
    @9
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @9
    cz
    wcel
    #
    wi
    @14
    @17
    @8
    @7
    cdvds
    wbr
    #
    @18
    @14
    @17
    @19
    wi
    @7
    cc0
    @14
    @7
    cc0
    wceq
    #
    wa
    #
    @19
    @17
    @21
    @8
    cc0
    @7
    cdvds
    @13
    @8
    cc0
    cdvds
    wbr
    #
    @12
    @20
    @13
    @8
    cz
    wcel
    #
    @22
    @8
    nnz
    #
    @8
    dvds0
    syl
    ad2antlr
    @14
    @20
    simpr
    breqtrrd
    a1d
    @14
    @7
    cc0
    wne
    #
    wa
    #
    @17
    @19
    @26
    @17
    @2
    @8
    cpc
    co
    #
    @2
    @7
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @19
    @26
    @16
    @29
    vp
    cprime
    @26
    @6
    wa
    #
    @16
    cc0
    @28
    @27
    cmin
    co
    #
    cle
    wbr
    @29
    @31
    @15
    @32
    cc0
    cle
    @31
    @6
    @12
    @25
    @13
    @15
    @32
    wceq
    @26
    @6
    simpr
    #
    @12
    @13
    @25
    @6
    simplll
    #
    @14
    @25
    @6
    simplr
    #
    @12
    @13
    @25
    @6
    simpllr
    #
    @7
    @8
    @2
    pcdiv
    syl121anc
    breq2d
    @31
    @28
    @27
    @31
    @28
    @31
    @6
    @12
    @25
    @28
    cn0
    wcel
    @33
    @34
    @35
    @2
    @7
    pczcl
    syl12anc
    nn0red
    @31
    @27
    @31
    @2
    @8
    @33
    @36
    pccld
    nn0red
    subge0d
    bitrd
    ralbidva
    @14
    @19
    @30
    wb
    #
    @25
    @13
    @23
    @12
    @37
    @12
    @24
    @12
    id
    @8
    @7
    vp
    pc2dvds
    syl2anr
    adantr
    bitr4d
    biimpd
    pm2.61dane
    @14
    @23
    @8
    cc0
    wne
    #
    @12
    @19
    @18
    wb
    @13
    @23
    @12
    @24
    adantl
    @13
    @38
    @12
    @8
    nnne0
    adantl
    @12
    @13
    simpl
    @8
    @7
    dvdsval2
    syl3anc
    sylibd
    @10
    @5
    @17
    @1
    @18
    @10
    @4
    @16
    vp
    cprime
    @10
    @3
    @15
    cc0
    cle
    cA
    @9
    @2
    cpc
    oveq2
    breq2d
    ralbidv
    cA
    @9
    cz
    eleq1
    imbi12d
    syl5ibrcom
    rexlimivv
    sylbi
    impbid2
end
