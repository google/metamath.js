include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "w3a.mm"
include "crest.mm"
include "co.mm"
include "cflim.mm"
include "cin.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
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
include "flimopn.mm"
include "simpll2.mm"
include "simpll3.mm"
include "elrestr.mm"
include "3expia.mm"
include "trfilss.mm"
include "sseld.mm"
include "inss1.mm"
include "a1i.mm"
include "simpl1.mm"
include "toponss.mm"
include "sylan.mm"
include "filss.mm"
include "3exp2.mm"
include "com24.mm"
include "syl3c.mm"
include "syld.mm"
include "impbid.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "simpl2.mm"
include "sselda.mm"
include "baibd.mm"
include "syl21anc.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl3.mm"
include "elrest.mm"
include "eleq2.mm"
include "elin.mm"
include "rbaib.mm"
include "adantl.mm"
include "sylan9bbr.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "ralxfr2d.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "ancom.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "eqrdv.mm"

theorem flimrest
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let cK: class K


  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) /\ Y e. F ) -> ( ( J |`t Y ) fLim ( F |`t Y ) ) = ( ( J fLim F ) i^i Y ) )

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
    cflim
    co
    #
    cJ
    cF
    cflim
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
    @7
    wcel
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
    @22
    wb
    @5
    @1
    cY
    cX
    wss
    #
    @23
    @1
    @3
    @4
    simp1
    @3
    @4
    @25
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
    @24
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
    @27
    @3
    @1
    @28
    @4
    cF
    cX
    filfbas
    3ad2ant2
    @1
    @3
    @4
    simp3
    cY
    cX
    cF
    cX
    fbncp
    syl2anc
    @5
    @3
    @25
    @24
    @27
    wb
    @1
    @3
    @4
    simp2
    @26
    cY
    cF
    cX
    trfil3
    syl2anc
    mpbird
    vy
    @11
    @7
    @6
    cY
    flimopn
    syl2anc
    @5
    @13
    @14
    @21
    @5
    @13
    wa
    #
    @11
    vz
    cv
    #
    wcel
    #
    @30
    cF
    wcel
    #
    wi
    #
    vz
    cJ
    wral
    #
    @31
    @30
    cY
    cin
    #
    @7
    wcel
    #
    wi
    #
    vz
    cJ
    wral
    @14
    @21
    @29
    @33
    @37
    vz
    cJ
    @29
    @30
    cJ
    wcel
    #
    wa
    #
    @32
    @36
    @31
    @39
    @32
    @36
    @39
    @3
    @4
    @32
    @36
    wi
    @1
    @3
    @4
    @13
    @38
    simpll2
    #
    @1
    @3
    @4
    @13
    @38
    simpll3
    #
    @3
    @4
    @32
    @36
    @30
    cY
    cF
    @2
    cF
    elrestr
    3expia
    syl2anc
    @39
    @36
    @35
    cF
    wcel
    #
    @32
    @39
    @7
    cF
    @35
    @39
    @3
    @4
    @7
    cF
    wss
    @40
    @41
    cY
    cF
    cX
    trfilss
    syl2anc
    sseld
    @39
    @3
    @35
    @30
    wss
    #
    @30
    cX
    wss
    #
    @42
    @32
    wi
    @40
    @43
    @39
    @30
    cY
    inss1
    a1i
    @29
    @1
    @38
    @44
    @1
    @3
    @4
    @13
    simpl1
    #
    @30
    cJ
    cX
    toponss
    sylan
    @3
    @42
    @44
    @43
    @32
    @3
    @42
    @44
    @43
    @32
    @35
    @30
    cF
    cX
    filss
    3exp2
    com24
    syl3c
    syld
    impbid
    imbi2d
    ralbidva
    @29
    @1
    @3
    @11
    cX
    wcel
    #
    @14
    @34
    wb
    @45
    @1
    @3
    @4
    @13
    simpl2
    @5
    cY
    cX
    @11
    @26
    sselda
    @1
    @3
    wa
    @14
    @46
    @34
    vz
    @11
    cF
    cJ
    cX
    flimopn
    baibd
    syl21anc
    @29
    @20
    @37
    vy
    vz
    @35
    @6
    cJ
    cvv
    @35
    cvv
    wcel
    @39
    @30
    cY
    vz
    vex
    inex1
    a1i
    @29
    @1
    @4
    @17
    @6
    wcel
    @17
    @35
    wceq
    #
    vz
    cJ
    wrex
    wb
    @45
    @1
    @3
    @4
    @13
    simpl3
    vz
    @17
    cY
    cJ
    @0
    cF
    elrest
    syl2anc
    @29
    @47
    wa
    @18
    @31
    @19
    @36
    @47
    @18
    @11
    @35
    wcel
    #
    @29
    @31
    @17
    @35
    @11
    eleq2
    @13
    @48
    @31
    wb
    @5
    @48
    @31
    @13
    @11
    @30
    cY
    elin
    rbaib
    adantl
    sylan9bbr
    @47
    @19
    @36
    wb
    @29
    @17
    @35
    @7
    eleq1
    adantl
    imbi12d
    ralxfr2d
    3bitr4d
    pm5.32da
    bitr4d
    @15
    @14
    @13
    wa
    @16
    @13
    @14
    ancom
    @11
    @9
    cY
    elin
    bitr4i
    syl6bb
    eqrdv
end
