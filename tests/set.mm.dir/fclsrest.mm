include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "w3a.mm"
include "crest.mm"
include "co.mm"
include "cfcls.mm"
include "cin.mm"
include "cv.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wi.mm"
include "wb.mm"
include "wss.mm"
include "simp1.mm"
include "filelss.mm"
include "3adant1.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "cdif.mm"
include "wn.mm"
include "cfbas.mm"
include "filfbas.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "fbncp.mm"
include "simp2.mm"
include "trfil3.mm"
include "mpbird.mm"
include "fclsopn.mm"
include "wceq.mm"
include "in32.mm"
include "ineq2.mm"
include "syl5eq.mm"
include "neeq1d.mm"
include "rspccv.mm"
include "inss1.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "ssn0.mm"
include "mpan.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "filin.mm"
include "syl3anc.mm"
include "inass.mm"
include "syl6eqr.mm"
include "rspcv.mm"
include "syl.mm"
include "ralrimdva.mm"
include "impbid2.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "a1i.mm"
include "wrex.mm"
include "elrest.mm"
include "3adant2.mm"
include "adantr.mm"
include "eleq2.mm"
include "elin.mm"
include "rbaib.mm"
include "adantl.mm"
include "sylan9bbr.mm"
include "ralxfr2d.mm"
include "ineq1.mm"
include "inindir.mm"
include "ralbidv.mm"
include "sylan9bb.mm"
include "imbi12d.mm"
include "sselda.mm"
include "baibd.mm"
include "syl21anc.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "ancom.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem fclsrest
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vo: setvar o
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cK: class K


  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) /\ Y e. F ) -> ( ( J |`t Y ) fClus ( F |`t Y ) ) = ( ( J fClus F ) i^i Y ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cY
    cF
    wcel
    #
    w3a
    #
    vx
    cJ
    cY
    crest
    co
    #
    cF
    cY
    crest
    co
    #
    cfcls
    co
    #
    cJ
    cF
    cfcls
    co
    #
    cY
    cin
    #
    @5
    vx
    cv
    #
    @8
    wcel
    #
    @11
    cY
    wcel
    #
    @11
    @9
    wcel
    #
    wa
    #
    @11
    @10
    wcel
    #
    @5
    @12
    @13
    @11
    vy
    cv
    #
    wcel
    #
    @17
    vz
    cv
    #
    cin
    #
    c0
    wne
    #
    vz
    @7
    wral
    #
    wi
    #
    vy
    @6
    wral
    #
    wa
    #
    @15
    @5
    @6
    cY
    ctopon
    cfv
    wcel
    #
    @7
    cY
    cfil
    cfv
    wcel
    #
    @12
    @25
    wb
    @5
    @1
    cY
    cX
    wss
    #
    @26
    @1
    @3
    @4
    simp1
    #
    @3
    @4
    @28
    @1
    cY
    cF
    cX
    filelss
    3adant1
    #
    cY
    cJ
    cX
    resttopon
    syl2anc
    @5
    @27
    cX
    cY
    cdif
    cF
    wcel
    wn
    #
    @5
    cF
    cX
    cfbas
    cfv
    wcel
    #
    @4
    @31
    @3
    @1
    @32
    @4
    cF
    cX
    filfbas
    3ad2ant2
    @1
    @3
    @4
    simp3
    #
    cY
    cX
    cF
    cX
    fbncp
    syl2anc
    @5
    @3
    @28
    @27
    @31
    wb
    @1
    @3
    @4
    simp2
    #
    @30
    cY
    cF
    cX
    trfil3
    syl2anc
    mpbird
    @11
    vy
    @7
    @6
    cY
    vz
    fclsopn
    syl2anc
    @5
    @13
    @24
    @14
    @5
    @13
    wa
    #
    @11
    vu
    cv
    #
    wcel
    #
    @36
    vs
    cv
    #
    cin
    cY
    cin
    #
    c0
    wne
    #
    vs
    cF
    wral
    #
    wi
    #
    vu
    cJ
    wral
    @37
    @36
    vt
    cv
    #
    cin
    #
    c0
    wne
    #
    vt
    cF
    wral
    #
    wi
    #
    vu
    cJ
    wral
    #
    @24
    @14
    @35
    @42
    @47
    vu
    cJ
    @35
    @36
    cJ
    wcel
    #
    wa
    #
    @41
    @46
    @37
    @50
    @41
    @46
    @41
    @45
    vt
    cF
    @41
    @43
    cF
    wcel
    @36
    cY
    cin
    #
    @43
    cin
    #
    c0
    wne
    #
    @45
    @40
    @53
    vs
    @43
    cF
    @38
    @43
    wceq
    #
    @39
    @52
    c0
    @54
    @39
    @51
    @38
    cin
    @52
    @36
    @38
    cY
    in32
    @38
    @43
    @51
    ineq2
    syl5eq
    neeq1d
    rspccv
    @52
    @44
    wss
    #
    @53
    @45
    @51
    @36
    wss
    @55
    @36
    cY
    inss1
    @51
    @36
    @43
    ssrin
    ax-mp
    @52
    @44
    ssn0
    mpan
    syl6
    ralrimiv
    @50
    @46
    @40
    vs
    cF
    @50
    @38
    cF
    wcel
    #
    wa
    #
    @38
    cY
    cin
    #
    cF
    wcel
    #
    @46
    @40
    wi
    @57
    @3
    @56
    @4
    @59
    @5
    @3
    @13
    @49
    @56
    @34
    ad3antrrr
    @50
    @56
    simpr
    @5
    @4
    @13
    @49
    @56
    @33
    ad3antrrr
    @38
    cY
    cF
    cX
    filin
    syl3anc
    @45
    @40
    vt
    @58
    cF
    @43
    @58
    wceq
    #
    @44
    @39
    c0
    @60
    @44
    @36
    @58
    cin
    @39
    @43
    @58
    @36
    ineq2
    @36
    @38
    cY
    inass
    syl6eqr
    neeq1d
    rspcv
    syl
    ralrimdva
    impbid2
    imbi2d
    ralbidva
    @35
    @23
    @42
    vy
    vu
    @51
    @6
    cJ
    cvv
    @51
    cvv
    wcel
    @50
    @36
    cY
    vu
    vex
    inex1
    a1i
    @5
    @17
    @6
    wcel
    @17
    @51
    wceq
    #
    vu
    cJ
    wrex
    wb
    #
    @13
    @1
    @4
    @62
    @3
    vu
    @17
    cY
    cJ
    @0
    cF
    elrest
    3adant2
    adantr
    @35
    @61
    wa
    @18
    @37
    @22
    @41
    @61
    @18
    @11
    @51
    wcel
    #
    @35
    @37
    @17
    @51
    @11
    eleq2
    @13
    @63
    @37
    wb
    @5
    @63
    @37
    @13
    @11
    @36
    cY
    elin
    rbaib
    adantl
    sylan9bbr
    @35
    @22
    @17
    @58
    cin
    #
    c0
    wne
    #
    vs
    cF
    wral
    @61
    @41
    @35
    @21
    @65
    vz
    vs
    @58
    @7
    cF
    cvv
    @58
    cvv
    wcel
    @35
    @56
    wa
    @38
    cY
    vs
    vex
    inex1
    a1i
    @5
    @19
    @7
    wcel
    @19
    @58
    wceq
    #
    vs
    cF
    wrex
    wb
    #
    @13
    @3
    @4
    @67
    @1
    vs
    @19
    cY
    cF
    @2
    cF
    elrest
    3adant1
    adantr
    @35
    @66
    wa
    @20
    @64
    c0
    @66
    @20
    @64
    wceq
    @35
    @19
    @58
    @17
    ineq2
    adantl
    neeq1d
    ralxfr2d
    @61
    @65
    @40
    vs
    cF
    @61
    @64
    @39
    c0
    @61
    @64
    @51
    @58
    cin
    @39
    @17
    @51
    @58
    ineq1
    @36
    @38
    cY
    inindir
    syl6eqr
    neeq1d
    ralbidv
    sylan9bb
    imbi12d
    ralxfr2d
    @35
    @1
    @3
    @11
    cX
    wcel
    #
    @14
    @48
    wb
    @5
    @1
    @13
    @29
    adantr
    @5
    @3
    @13
    @34
    adantr
    @5
    cY
    cX
    @11
    @30
    sselda
    @1
    @3
    wa
    @14
    @68
    @48
    @11
    vu
    cF
    cJ
    cX
    vt
    fclsopn
    baibd
    syl21anc
    3bitr4d
    pm5.32da
    bitrd
    @16
    @14
    @13
    wa
    @15
    @11
    @9
    cY
    elin
    @14
    @13
    ancom
    bitri
    syl6bbr
    eqrdv
end
