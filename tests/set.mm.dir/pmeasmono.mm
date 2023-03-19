include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "c0.mm"
include "wss.mm"
include "eqimss.mm"
include "ssdifeq0.mm"
include "sylib.mm"
include "fveq2d.mm"
include "adantl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "ffvelrnd.mm"
include "cxr.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "wne.mm"
include "cxad.mm"
include "iccssxr.mm"
include "wf.mm"
include "sseldi.mm"
include "xrge0addge.mm"
include "syl2anc.mm"
include "cpr.mm"
include "cuni.mm"
include "cv.mm"
include "cesum.mm"
include "com.mm"
include "cdom.mm"
include "wdisj.mm"
include "w3a.mm"
include "prct.mm"
include "prssi.mm"
include "cin.mm"
include "disjdif.mm"
include "wb.mm"
include "simpr.mm"
include "id.mm"
include "disjprg.mm"
include "syl3anc.mm"
include "mpbiri.mm"
include "3jca.mm"
include "cvv.mm"
include "wi.mm"
include "prex.mm"
include "biidd.mm"
include "breq1.mm"
include "sseq1.mm"
include "disjeq1.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "unieq.mm"
include "esumeq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "ax-mp.mm"
include "adantlr.mm"
include "mpdan.mm"
include "cun.mm"
include "uniprg.mm"
include "undif.mm"
include "esumpr.mm"
include "3eqtr3d.mm"
include "breqtrrd.mm"
include "pm2.61dane.mm"

theorem pmeasmono
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  assume caraext.1: |- ( ph -> P : R --> ( 0 [,] +oo ) )
  assume caraext.2: |- ( ph -> ( P ` (/) ) = 0 )
  assume caraext.3: |- ( ( ph /\ ( x ~<_ _om /\ x C_ R /\ Disj_ y e. x y ) ) -> ( P ` U. x ) = sum* y e. x ( P ` y ) )
  assume pmeasmono.1: |- ( ph -> A e. R )
  assume pmeasmono.2: |- ( ph -> B e. R )
  assume pmeasmono.3: |- ( ph -> ( B \ A ) e. R )
  assume pmeasmono.4: |- ( ph -> A C_ B )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint P x
  disjoint P y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( P ` A ) <_ ( P ` B ) )

  proof
    wph
    cA
    cP
    cfv
    #
    cB
    cP
    cfv
    #
    cle
    wbr
    cA
    cB
    cA
    cdif
    #
    wph
    cA
    @2
    wceq
    #
    wa
    #
    @0
    cc0
    @1
    cle
    @4
    @0
    c0
    cP
    cfv
    #
    cc0
    @3
    @0
    @5
    wceq
    wph
    @3
    cA
    c0
    cP
    @3
    cA
    @2
    wss
    cA
    c0
    wceq
    cA
    @2
    eqimss
    cA
    cB
    ssdifeq0
    sylib
    fveq2d
    adantl
    wph
    @5
    cc0
    wceq
    @3
    caraext.2
    adantr
    eqtrd
    wph
    cc0
    @1
    cle
    wbr
    #
    @3
    wph
    @1
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @6
    wph
    cR
    @7
    cB
    cP
    caraext.1
    pmeasmono.2
    ffvelrnd
    @8
    @1
    cxr
    wcel
    @6
    @1
    elxrge0
    simprbi
    syl
    adantr
    eqbrtrd
    wph
    cA
    @2
    wne
    #
    wa
    #
    @0
    @0
    @2
    cP
    cfv
    #
    cxad
    co
    #
    @1
    cle
    @10
    @0
    cxr
    wcel
    @11
    @7
    wcel
    @0
    @12
    cle
    wbr
    @10
    @7
    cxr
    @0
    cc0
    cpnf
    iccssxr
    @10
    cR
    @7
    cA
    cP
    wph
    cR
    @7
    cP
    wf
    @9
    caraext.1
    adantr
    #
    wph
    cA
    cR
    wcel
    #
    @9
    pmeasmono.1
    adantr
    #
    ffvelrnd
    #
    sseldi
    @10
    cR
    @7
    @2
    cP
    @13
    wph
    @2
    cR
    wcel
    #
    @9
    pmeasmono.3
    adantr
    #
    ffvelrnd
    #
    @0
    @11
    xrge0addge
    syl2anc
    @10
    cA
    @2
    cpr
    #
    cuni
    #
    cP
    cfv
    #
    @20
    vy
    cv
    #
    cP
    cfv
    #
    vy
    cesum
    #
    @1
    @12
    @10
    @20
    com
    cdom
    wbr
    #
    @20
    cR
    wss
    #
    vy
    @20
    @23
    wdisj
    #
    w3a
    #
    @22
    @25
    wceq
    #
    @10
    @26
    @27
    @28
    wph
    @26
    @9
    wph
    @14
    @17
    @26
    pmeasmono.1
    pmeasmono.3
    cA
    @2
    cR
    cR
    prct
    syl2anc
    adantr
    wph
    @27
    @9
    wph
    @14
    @17
    @27
    pmeasmono.1
    pmeasmono.3
    cA
    @2
    cR
    prssi
    syl2anc
    adantr
    @10
    @28
    cA
    @2
    cin
    c0
    wceq
    #
    cA
    cB
    disjdif
    @10
    @14
    @17
    @9
    @28
    @31
    wb
    @15
    @18
    wph
    @9
    simpr
    #
    vy
    cA
    @2
    @23
    cA
    @2
    cR
    @23
    cA
    wceq
    #
    id
    @23
    @2
    wceq
    #
    id
    disjprg
    syl3anc
    mpbiri
    3jca
    wph
    @29
    @30
    @9
    @20
    cvv
    wcel
    wph
    @29
    wa
    #
    @30
    wi
    #
    cA
    @2
    prex
    wph
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @37
    cR
    wss
    #
    vy
    @37
    @23
    wdisj
    #
    w3a
    #
    wa
    #
    @37
    cuni
    #
    cP
    cfv
    #
    @37
    @24
    vy
    cesum
    #
    wceq
    #
    wi
    @36
    vx
    @20
    cvv
    @37
    @20
    wceq
    #
    @42
    @35
    @46
    @30
    @47
    wph
    wph
    @41
    @29
    @47
    wph
    biidd
    @47
    @38
    @26
    @39
    @27
    @40
    @28
    @37
    @20
    com
    cdom
    breq1
    @37
    @20
    cR
    sseq1
    vy
    @37
    @20
    @23
    disjeq1
    3anbi123d
    anbi12d
    @47
    @44
    @22
    @45
    @25
    @47
    @43
    @21
    cP
    @37
    @20
    unieq
    fveq2d
    @37
    @20
    @24
    vy
    esumeq1
    eqeq12d
    imbi12d
    caraext.3
    vtoclg
    ax-mp
    adantlr
    mpdan
    @10
    @21
    cB
    cP
    wph
    @21
    cB
    wceq
    @9
    wph
    @21
    cA
    @2
    cun
    #
    cB
    wph
    @14
    @17
    @21
    @48
    wceq
    pmeasmono.1
    pmeasmono.3
    cA
    @2
    cR
    cR
    uniprg
    syl2anc
    wph
    cA
    cB
    wss
    @48
    cB
    wceq
    pmeasmono.4
    cA
    cB
    undif
    sylib
    eqtrd
    adantr
    fveq2d
    @10
    cA
    @2
    @24
    @0
    vy
    @11
    cR
    cR
    @10
    @33
    wa
    @23
    cA
    cP
    @10
    @33
    simpr
    fveq2d
    @10
    @34
    wa
    @23
    @2
    cP
    @10
    @34
    simpr
    fveq2d
    @15
    @18
    @16
    @19
    @32
    esumpr
    3eqtr3d
    breqtrrd
    pm2.61dane
end
