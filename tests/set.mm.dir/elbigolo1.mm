include "cr.mm"
include "wss.mm"
include "crp.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cfdiv.mm"
include "cbigo.mm"
include "wcel.mm"
include "clo1.mm"
include "wa.mm"
include "cdiv.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "id.mm"
include "rpssre.mm"
include "a1i.mm"
include "fssd.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "simplrr.mm"
include "simpl2.mm"
include "rpregt0d.mm"
include "3jca.mm"
include "ledivmul2.mm"
include "bicomd.mm"
include "syl.mm"
include "cvv.mm"
include "csupp.mm"
include "wceq.mm"
include "3ad2ant2.mm"
include "reex.mm"
include "ssex.mm"
include "3ad2ant1.mm"
include "cdm.mm"
include "wfun.mm"
include "crn.mm"
include "wnel.mm"
include "ffun.mm"
include "adantl.mm"
include "anim1i.mm"
include "ancomd.mm"
include "fex.mm"
include "0red.mm"
include "frn.mm"
include "wn.mm"
include "0nrp.mm"
include "ssneld.mm"
include "mpi.mm"
include "df-nel.mm"
include "sylibr.mm"
include "suppdm.mm"
include "syl31anc.mm"
include "fdm.mm"
include "eqtrd.mm"
include "3adant3.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "refdivmptfv.mm"
include "syl2anc.mm"
include "breq1d.mm"
include "bitr4d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "2rexbidva.mm"
include "simp1.mm"
include "ssid.mm"
include "elbigo2.mm"
include "syl22anc.mm"
include "refdivmptf.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "feq2d.mm"
include "mpbird.mm"
include "ello12.mm"
include "3bitr4d.mm"

theorem elbigolo1
  let cA: class A
  let cF: class F
  let cG: class G
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( ( A C_ RR /\ G : A --> RR+ /\ F : A --> RR+ ) -> ( F e. ( _O ` G ) <-> ( F /_f G ) e. <_O(1) ) )

  proof
    cA
    cr
    wss
    #
    cA
    crp
    cG
    wf
    #
    cA
    crp
    cF
    wf
    #
    w3a
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @5
    cF
    cfv
    #
    vm
    cv
    #
    @5
    cG
    cfv
    #
    cmul
    co
    cle
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    vm
    cr
    wrex
    vx
    cr
    wrex
    #
    @6
    @5
    cF
    cG
    cfdiv
    co
    #
    cfv
    #
    @8
    cle
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    vm
    cr
    wrex
    vx
    cr
    wrex
    #
    cF
    cG
    cbigo
    cfv
    wcel
    #
    @14
    clo1
    wcel
    #
    @3
    @12
    @18
    vx
    vm
    cr
    cr
    @3
    @4
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    wa
    #
    wa
    #
    @11
    @17
    vy
    cA
    @25
    @5
    cA
    wcel
    #
    wa
    #
    @10
    @16
    @6
    @27
    @10
    @7
    @9
    cdiv
    co
    #
    @8
    cle
    wbr
    #
    @16
    @27
    @7
    cr
    wcel
    #
    @23
    @9
    cr
    wcel
    cc0
    @9
    clt
    wbr
    wa
    #
    w3a
    #
    @10
    @29
    wb
    @27
    @30
    @23
    @31
    @25
    cA
    cr
    @5
    cF
    @3
    cA
    cr
    cF
    wf
    #
    @24
    @2
    @0
    @33
    @1
    @2
    cA
    crp
    cr
    cF
    @2
    id
    crp
    cr
    wss
    #
    @2
    rpssre
    a1i
    fssd
    3ad2ant3
    #
    adantr
    ffvelrnda
    @3
    @22
    @23
    @26
    simplrr
    @27
    @9
    @25
    cA
    crp
    @5
    cG
    @0
    @1
    @2
    @24
    simpl2
    ffvelrnda
    rpregt0d
    3jca
    @32
    @29
    @10
    @7
    @8
    @9
    ledivmul2
    bicomd
    syl
    @27
    @15
    @28
    @8
    cle
    @27
    @33
    cA
    cr
    cG
    wf
    #
    cA
    cvv
    wcel
    #
    w3a
    #
    @5
    cG
    cc0
    csupp
    co
    #
    wcel
    #
    @15
    @28
    wceq
    @25
    @38
    @26
    @3
    @38
    @24
    @3
    @33
    @36
    @37
    @35
    @1
    @0
    @36
    @2
    @1
    cA
    crp
    cr
    cG
    @1
    id
    @34
    @1
    rpssre
    a1i
    fssd
    3ad2ant2
    #
    @0
    @1
    @37
    @2
    cA
    cr
    reex
    ssex
    #
    3ad2ant1
    3jca
    #
    adantr
    adantr
    @25
    @26
    @40
    @25
    cA
    @39
    @5
    @3
    cA
    @39
    wceq
    @24
    @3
    @39
    cA
    @0
    @1
    @39
    cA
    wceq
    @2
    @0
    @1
    wa
    #
    @39
    cG
    cdm
    #
    cA
    @44
    cG
    wfun
    #
    cG
    cvv
    wcel
    #
    cc0
    cr
    wcel
    #
    cc0
    cG
    crn
    #
    wnel
    #
    @39
    @45
    wceq
    #
    @1
    @46
    @0
    cA
    crp
    cG
    ffun
    adantl
    #
    @44
    @1
    @37
    wa
    @47
    @44
    @37
    @1
    @0
    @37
    @1
    @42
    anim1i
    ancomd
    cA
    crp
    cvv
    cG
    fex
    #
    syl
    @44
    0red
    #
    @1
    @50
    @0
    @1
    @49
    crp
    wss
    #
    @50
    cA
    crp
    cG
    frn
    @55
    cc0
    @49
    wcel
    wn
    #
    @50
    @55
    cc0
    crp
    wcel
    wn
    @56
    0nrp
    @55
    @49
    crp
    cc0
    @55
    id
    ssneld
    mpi
    cc0
    @49
    df-nel
    sylibr
    syl
    adantl
    #
    cG
    cvv
    cr
    cc0
    suppdm
    #
    syl31anc
    @1
    @45
    cA
    wceq
    @0
    cA
    crp
    cG
    fdm
    #
    adantl
    eqtrd
    3adant3
    eqcomd
    adantr
    eleq2d
    biimpa
    cA
    cF
    cG
    cvv
    @5
    refdivmptfv
    syl2anc
    breq1d
    bitr4d
    imbi2d
    ralbidva
    2rexbidva
    @3
    @36
    @0
    @33
    cA
    cA
    wss
    #
    @20
    @13
    wb
    @41
    @0
    @1
    @2
    simp1
    #
    @35
    @60
    @3
    cA
    ssid
    a1i
    vx
    vy
    cA
    cA
    vm
    cF
    cG
    elbigo2
    syl22anc
    @3
    cA
    cr
    @14
    wf
    #
    @0
    @21
    @19
    wb
    @3
    @62
    @39
    cr
    @14
    wf
    #
    @3
    @38
    @63
    @43
    cA
    cF
    cG
    cvv
    refdivmptf
    syl
    @3
    cA
    @39
    cr
    @14
    @3
    cA
    @45
    @39
    @1
    @0
    cA
    @45
    wceq
    @2
    @1
    @45
    cA
    @59
    eqcomd
    3ad2ant2
    @0
    @1
    @51
    @2
    @44
    @46
    @47
    @48
    @50
    @51
    @52
    @44
    @1
    @37
    @47
    @0
    @1
    simpr
    @0
    @37
    @1
    @42
    adantr
    @53
    syl2anc
    @54
    @57
    @58
    syl31anc
    3adant3
    eqtr4d
    feq2d
    mpbird
    @61
    vx
    vy
    cA
    vm
    @14
    ello12
    syl2anc
    3bitr4d
end
