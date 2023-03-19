include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "con0.mm"
include "cin.mm"
include "cen.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "pwexg.mm"
include "rabexg.mm"
include "incom.mm"
include "inex1g.mm"
include "syl5eqelr.mm"
include "word.mm"
include "wtr.mm"
include "wi.mm"
include "wal.mm"
include "inss1.mm"
include "sseli.mm"
include "onelon.mm"
include "ancoms.mm"
include "sylan2.mm"
include "onelss.mm"
include "impcom.mm"
include "inss2.mm"
include "breq1.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "elpwid.mm"
include "adantl.mm"
include "sstrd.mm"
include "selpw.mm"
include "sylibr.mm"
include "cdom.mm"
include "vex.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "simprd.mm"
include "domsdomtr.mm"
include "syl2anc.mm"
include "sylanbrc.mm"
include "elind.mm"
include "gen2.mm"
include "dftr2.mm"
include "mpbir.mm"
include "ordon.mm"
include "trssord.mm"
include "mp3an.mm"
include "elong.mm"
include "mpbiri.mm"
include "4syl.mm"
include "adantr.mm"
include "wn.mm"
include "simpr.mm"
include "syl5ss.mm"
include "mpd.mm"
include "ordirr.mm"
include "mp1i.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "3adant3.mm"
include "simp3.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfin.mm"
include "nfbr.mm"
include "elrabf.mm"
include "3expia.mm"
include "mtod.mm"
include "bren2.mm"
include "isnumi.mm"

theorem tskwe
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  assert |- ( ( A e. V /\ { x e. ~P A | x ~< A } C_ A ) -> A e. dom card )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
    cA
    csdm
    wbr
    #
    vx
    cA
    cpw
    #
    crab
    #
    cA
    wss
    #
    wa
    #
    con0
    @4
    cin
    #
    con0
    wcel
    #
    @7
    cA
    cen
    wbr
    #
    cA
    ccrd
    cdm
    wcel
    @0
    @8
    @5
    @0
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    #
    @7
    cvv
    wcel
    #
    @8
    cA
    cV
    pwexg
    @2
    vx
    @3
    cvv
    rabexg
    @10
    @7
    @4
    con0
    cin
    cvv
    @4
    con0
    incom
    @4
    con0
    cvv
    inex1g
    syl5eqelr
    @11
    @8
    @7
    word
    #
    @7
    wtr
    #
    @7
    con0
    wss
    con0
    word
    @12
    @13
    vy
    cv
    #
    vz
    cv
    #
    wcel
    #
    @15
    @7
    wcel
    #
    wa
    #
    @14
    @7
    wcel
    wi
    #
    vz
    wal
    vy
    wal
    @19
    vy
    vz
    @18
    con0
    @4
    @14
    @17
    @16
    @15
    con0
    wcel
    #
    @14
    con0
    wcel
    #
    @7
    con0
    @15
    con0
    @4
    inss1
    #
    sseli
    #
    @20
    @16
    @21
    @15
    @14
    onelon
    ancoms
    sylan2
    @18
    @14
    @3
    wcel
    #
    @14
    cA
    csdm
    wbr
    #
    @14
    @4
    wcel
    @18
    @14
    cA
    wss
    @24
    @18
    @14
    @15
    cA
    @17
    @16
    @20
    @14
    @15
    wss
    #
    @23
    @20
    @16
    @26
    @15
    @14
    onelss
    impcom
    sylan2
    #
    @17
    @15
    cA
    wss
    @16
    @17
    @15
    cA
    @17
    @15
    @3
    wcel
    #
    @15
    cA
    csdm
    wbr
    #
    @17
    @15
    @4
    wcel
    @28
    @29
    wa
    @7
    @4
    @15
    con0
    @4
    inss2
    #
    sseli
    @2
    @29
    vx
    @15
    @3
    @1
    @15
    cA
    csdm
    breq1
    elrab
    sylib
    #
    simpld
    elpwid
    adantl
    sstrd
    vy
    cA
    selpw
    sylibr
    @18
    @14
    @15
    cdom
    wbr
    #
    @29
    @25
    @15
    cvv
    wcel
    @18
    @26
    @32
    vz
    vex
    @27
    @14
    @15
    cvv
    ssdomg
    mpsyl
    @17
    @29
    @16
    @17
    @28
    @29
    @31
    simprd
    adantl
    @14
    @15
    cA
    domsdomtr
    syl2anc
    @2
    @25
    vx
    @14
    @3
    @1
    @14
    cA
    csdm
    breq1
    elrab
    sylanbrc
    elind
    gen2
    vy
    vz
    @7
    dftr2
    mpbir
    @22
    ordon
    @7
    con0
    trssord
    mp3an
    #
    @7
    cvv
    elong
    mpbiri
    4syl
    #
    adantr
    @6
    @7
    cA
    cdom
    wbr
    #
    @7
    cA
    csdm
    wbr
    #
    wn
    @9
    @6
    @7
    cA
    wss
    #
    @35
    @6
    @7
    @4
    cA
    @30
    @0
    @5
    simpr
    syl5ss
    #
    @0
    @37
    @35
    wi
    @5
    @7
    cA
    cV
    ssdomg
    adantr
    mpd
    @6
    @36
    @7
    @7
    wcel
    #
    @12
    @39
    wn
    @6
    @33
    @7
    ordirr
    mp1i
    @0
    @5
    @36
    @39
    @0
    @5
    @36
    w3a
    #
    con0
    @4
    @7
    @0
    @5
    @8
    @36
    @34
    3ad2ant1
    @40
    @7
    @3
    wcel
    #
    @36
    @7
    @4
    wcel
    @0
    @5
    @41
    @36
    @6
    @41
    @37
    @38
    @0
    @41
    @37
    wb
    @5
    @7
    cA
    cV
    elpw2g
    adantr
    mpbird
    3adant3
    @0
    @5
    @36
    simp3
    @2
    @36
    vx
    @7
    @3
    vx
    con0
    @4
    vx
    con0
    nfcv
    @2
    vx
    @3
    nfrab1
    nfin
    #
    vx
    @3
    nfcv
    vx
    @7
    cA
    csdm
    @42
    vx
    csdm
    nfcv
    vx
    cA
    nfcv
    nfbr
    @1
    @7
    cA
    csdm
    breq1
    elrabf
    sylanbrc
    elind
    3expia
    mtod
    @7
    cA
    bren2
    sylanbrc
    @7
    cA
    isnumi
    syl2anc
end
