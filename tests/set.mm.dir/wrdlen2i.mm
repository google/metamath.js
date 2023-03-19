include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "wceq.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cvv.mm"
include "wne.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "simpl.mm"
include "0ne1.mm"
include "a1i.mm"
include "fprg.mm"
include "mp3an2i.mm"
include "wi.mm"
include "fzo0to2pr.mm"
include "eqcomi.mm"
include "feq2d.mm"
include "biimpa.mm"
include "wss.mm"
include "prssi.mm"
include "adantr.mm"
include "fssd.mm"
include "ex.mm"
include "impcom.mm"
include "wb.mm"
include "feq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "mpancom.mm"
include "iswrdi.mm"
include "syl.mm"
include "fveq2.mm"
include "neii.mm"
include "opth1g.mm"
include "sylancr.mm"
include "mtoi.mm"
include "neqned.mm"
include "opex.mm"
include "hashprg.mm"
include "mp1i.mm"
include "mpbid.mm"
include "sylan9eqr.mm"
include "fvpr1g.mm"
include "simpr.mm"
include "fvpr2g.mm"
include "jca.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "jca31.mm"

theorem wrdlen2i
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W


  assert |- ( ( S e. V /\ T e. V ) -> ( W = { <. 0 , S >. , <. 1 , T >. } -> ( ( W e. Word V /\ ( # ` W ) = 2 ) /\ ( ( W ` 0 ) = S /\ ( W ` 1 ) = T ) ) ) )

  proof
    cS
    cV
    wcel
    #
    cT
    cV
    wcel
    #
    wa
    #
    cW
    cc0
    cS
    cop
    #
    c1
    cT
    cop
    #
    cpr
    #
    wceq
    #
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    cc0
    cW
    cfv
    #
    cS
    wceq
    #
    c1
    cW
    cfv
    #
    cT
    wceq
    #
    wa
    #
    wa
    @2
    @6
    wa
    #
    @7
    @9
    @14
    @15
    cc0
    c2
    cfzo
    co
    #
    cV
    cW
    wf
    #
    @7
    cc0
    c1
    cpr
    #
    cS
    cT
    cpr
    #
    @5
    wf
    #
    @15
    @17
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    @15
    @2
    cc0
    c1
    wne
    #
    @20
    @21
    @22
    c0ex
    1ex
    pm3.2i
    @2
    @6
    simpl
    @23
    @15
    0ne1
    a1i
    cc0
    c1
    cS
    cT
    cvv
    cvv
    cV
    cV
    fprg
    mp3an2i
    @20
    @15
    wa
    @17
    @16
    cV
    @5
    wf
    #
    @15
    @20
    @24
    @2
    @20
    @24
    wi
    @6
    @2
    @20
    @24
    @2
    @20
    wa
    @16
    @19
    cV
    @5
    @2
    @20
    @16
    @19
    @5
    wf
    @2
    @18
    @16
    @19
    @5
    @18
    @16
    wceq
    @2
    @16
    @18
    fzo0to2pr
    eqcomi
    a1i
    feq2d
    biimpa
    @2
    @19
    cV
    wss
    @20
    cS
    cT
    cV
    prssi
    adantr
    fssd
    ex
    adantr
    impcom
    @15
    @17
    @24
    wb
    #
    @20
    @6
    @25
    @2
    @16
    cV
    cW
    @5
    feq1
    adantl
    adantl
    mpbird
    mpancom
    cV
    c2
    cW
    iswrdi
    syl
    @6
    @2
    @8
    @5
    chash
    cfv
    #
    c2
    cW
    @5
    chash
    fveq2
    @2
    @3
    @4
    wne
    #
    @26
    c2
    wceq
    #
    @2
    @3
    @4
    @2
    @3
    @4
    wceq
    #
    cc0
    c1
    wceq
    #
    cc0
    c1
    0ne1
    neii
    @2
    @21
    @0
    @29
    @30
    wi
    c0ex
    @0
    @1
    simpl
    #
    cc0
    cS
    c1
    cT
    cvv
    cV
    opth1g
    sylancr
    mtoi
    neqned
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    wa
    @27
    @28
    wb
    @2
    @32
    @33
    cc0
    cS
    opex
    c1
    cT
    opex
    pm3.2i
    @3
    @4
    cvv
    cvv
    hashprg
    mp1i
    mpbid
    sylan9eqr
    @15
    @14
    cc0
    @5
    cfv
    #
    cS
    wceq
    #
    c1
    @5
    cfv
    #
    cT
    wceq
    #
    wa
    #
    @2
    @38
    @6
    @2
    @35
    @37
    @21
    @2
    @0
    @23
    @35
    c0ex
    @31
    @23
    @2
    0ne1
    a1i
    #
    cc0
    c1
    cS
    cT
    cvv
    cV
    fvpr1g
    mp3an2i
    @22
    @2
    @1
    @23
    @37
    1ex
    @0
    @1
    simpr
    @39
    cc0
    c1
    cS
    cT
    cvv
    cV
    fvpr2g
    mp3an2i
    jca
    adantr
    @6
    @14
    @38
    wb
    @2
    @6
    @11
    @35
    @13
    @37
    @6
    @10
    @34
    cS
    cc0
    cW
    @5
    fveq1
    eqeq1d
    @6
    @12
    @36
    cT
    c1
    cW
    @5
    fveq1
    eqeq1d
    anbi12d
    adantl
    mpbird
    jca31
    ex
end
