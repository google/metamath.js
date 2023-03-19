include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "simpll1.mm"
include "simplr.mm"
include "simpr.mm"
include "cc0.mm"
include "cdif.mm"
include "disj3.mm"
include "biimpi.mm"
include "difeq1.mm"
include "difid.mm"
include "syl6eq.mm"
include "sylan9eqr.mm"
include "eqtr2.mm"
include "syldan.mm"
include "uneq12d.mm"
include "unidm.mm"
include "fveq2d.mm"
include "probnul.mm"
include "oveq12d.mm"
include "00id.mm"
include "eqtr4d.mm"
include "syl12anc.mm"
include "ex.mm"
include "wne.mm"
include "cxad.mm"
include "3anass.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "cpr.mm"
include "cuni.mm"
include "cv.mm"
include "cesum.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "simpl1.mm"
include "wss.mm"
include "prssi.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "prex.mm"
include "elpw.mm"
include "sylibr.mm"
include "prct.mm"
include "wb.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3.mm"
include "id.mm"
include "disjprg.mm"
include "syl3anc.mm"
include "biimpar.mm"
include "probcun.mm"
include "syl112anc.mm"
include "uniprg.mm"
include "fveq2.mm"
include "adantl.mm"
include "c1.mm"
include "cicc.mm"
include "cpnf.mm"
include "unitssxrge0.mm"
include "simp1.mm"
include "prob01.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "esumpr.mm"
include "eqeq12d.mm"
include "mpbid.mm"
include "sylanb.mm"
include "cr.mm"
include "unitssre.mm"
include "simpll2.mm"
include "simpll3.mm"
include "rexadd.mm"
include "eqtrd.mm"
include "pm2.61dane.mm"

theorem probun
  let cA: class A
  let cB: class B
  let cP: class P
  let vx: setvar x


  assert |- ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) -> ( ( A i^i B ) = (/) -> ( P ` ( A u. B ) ) = ( ( P ` A ) + ( P ` B ) ) ) )

  proof
    cP
    cprb
    wcel
    #
    cA
    cP
    cdm
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cA
    cB
    cin
    c0
    wceq
    #
    cA
    cB
    cun
    #
    cP
    cfv
    #
    cA
    cP
    cfv
    #
    cB
    cP
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    cA
    cB
    @4
    cA
    cB
    wceq
    #
    wa
    #
    @5
    @11
    @13
    @5
    wa
    @0
    @12
    @5
    @11
    @0
    @2
    @3
    @12
    @5
    simpll1
    @4
    @12
    @5
    simplr
    @13
    @5
    simpr
    @0
    @12
    @5
    wa
    #
    wa
    #
    @7
    cc0
    @10
    @14
    @0
    @7
    c0
    cP
    cfv
    #
    cc0
    @14
    @6
    c0
    cP
    @14
    @6
    c0
    c0
    cun
    c0
    @14
    cA
    c0
    cB
    c0
    @5
    @12
    cA
    cA
    cB
    cdif
    #
    c0
    @5
    cA
    @17
    wceq
    cA
    cB
    disj3
    biimpi
    @12
    @17
    cB
    cB
    cdif
    c0
    cA
    cB
    cB
    difeq1
    cB
    difid
    syl6eq
    sylan9eqr
    #
    @12
    @5
    cA
    c0
    wceq
    cB
    c0
    wceq
    @18
    cA
    cB
    c0
    eqtr2
    syldan
    #
    uneq12d
    c0
    unidm
    syl6eq
    fveq2d
    cP
    probnul
    #
    sylan9eqr
    @15
    @10
    cc0
    cc0
    caddc
    co
    cc0
    @15
    @8
    cc0
    @9
    cc0
    caddc
    @14
    @0
    @8
    @16
    cc0
    @14
    cA
    c0
    cP
    @18
    fveq2d
    @20
    sylan9eqr
    @14
    @0
    @9
    @16
    cc0
    @14
    cB
    c0
    cP
    @19
    fveq2d
    @20
    sylan9eqr
    oveq12d
    00id
    syl6eq
    eqtr4d
    syl12anc
    ex
    @4
    cA
    cB
    wne
    #
    wa
    #
    @5
    @11
    @22
    @5
    wa
    #
    @7
    @8
    @9
    cxad
    co
    #
    @10
    @22
    @0
    @2
    @3
    wa
    #
    @21
    w3a
    #
    @5
    @7
    @24
    wceq
    #
    @22
    @0
    @25
    wa
    #
    @21
    wa
    @26
    @4
    @28
    @21
    @0
    @2
    @3
    3anass
    anbi1i
    @0
    @25
    @21
    df-3an
    bitr4i
    @26
    @5
    wa
    #
    cA
    cB
    cpr
    #
    cuni
    #
    cP
    cfv
    #
    @30
    vx
    cv
    #
    cP
    cfv
    #
    vx
    cesum
    #
    wceq
    #
    @27
    @29
    @0
    @30
    @1
    cpw
    wcel
    #
    @30
    com
    cdom
    wbr
    #
    vx
    @30
    @33
    wdisj
    #
    @36
    @0
    @25
    @21
    @5
    simpl1
    @29
    @30
    @1
    wss
    #
    @37
    @26
    @40
    @5
    @25
    @0
    @40
    @21
    cA
    cB
    @1
    prssi
    3ad2ant2
    adantr
    @30
    @1
    cA
    cB
    prex
    elpw
    sylibr
    @26
    @38
    @5
    @25
    @0
    @38
    @21
    cA
    cB
    @1
    @1
    prct
    3ad2ant2
    adantr
    @26
    @39
    @5
    @26
    @2
    @3
    @21
    @39
    @5
    wb
    @0
    @2
    @3
    @21
    simp2l
    #
    @0
    @2
    @3
    @21
    simp2r
    #
    @0
    @25
    @21
    simp3
    #
    vx
    cA
    cB
    @33
    cA
    cB
    @1
    @33
    cA
    wceq
    #
    id
    @33
    cB
    wceq
    #
    id
    disjprg
    syl3anc
    biimpar
    vx
    @30
    cP
    probcun
    syl112anc
    @26
    @36
    @27
    wb
    @5
    @26
    @32
    @7
    @35
    @24
    @25
    @0
    @32
    @7
    wceq
    @21
    @25
    @31
    @6
    cP
    cA
    cB
    @1
    @1
    uniprg
    fveq2d
    3ad2ant2
    @26
    cA
    cB
    @34
    @8
    vx
    @9
    @1
    @1
    @44
    @34
    @8
    wceq
    @26
    @33
    cA
    cP
    fveq2
    adantl
    @45
    @34
    @9
    wceq
    @26
    @33
    cB
    cP
    fveq2
    adantl
    @41
    @42
    @26
    cc0
    c1
    cicc
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    @8
    unitssxrge0
    @26
    @0
    @2
    @8
    @46
    wcel
    #
    @0
    @25
    @21
    simp1
    #
    @41
    cA
    cP
    prob01
    #
    syl2anc
    sseldi
    @26
    @46
    @47
    @9
    unitssxrge0
    @26
    @0
    @3
    @9
    @46
    wcel
    #
    @49
    @42
    cB
    cP
    prob01
    #
    syl2anc
    sseldi
    @43
    esumpr
    eqeq12d
    adantr
    mpbid
    sylanb
    @23
    @8
    cr
    wcel
    @9
    cr
    wcel
    @24
    @10
    wceq
    @23
    @46
    cr
    @8
    unitssre
    @23
    @0
    @2
    @48
    @0
    @2
    @3
    @21
    @5
    simpll1
    #
    @0
    @2
    @3
    @21
    @5
    simpll2
    @50
    syl2anc
    sseldi
    @23
    @46
    cr
    @9
    unitssre
    @23
    @0
    @3
    @51
    @53
    @0
    @2
    @3
    @21
    @5
    simpll3
    @52
    syl2anc
    sseldi
    @8
    @9
    rexadd
    syl2anc
    eqtrd
    ex
    pm2.61dane
end
