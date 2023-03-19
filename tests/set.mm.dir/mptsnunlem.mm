include "wss.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "cmpt.mm"
include "reseq1i.mm"
include "resmpt.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rnmptsn.mm"
include "syl6eq.mm"
include "unieqd.mm"
include "eleq2d.mm"
include "eleq1.mm"
include "wa.mm"
include "wex.mm"
include "eluniab.mm"
include "ancom.mm"
include "r19.41v.mm"
include "df-rex.mm"
include "3bitr2i.mm"
include "wb.mm"
include "eleq2.mm"
include "anbi2d.mm"
include "adantr.mm"
include "ibi.mm"
include "anim2i.mm"
include "eximi.mm"
include "sylbi.mm"
include "an12.mm"
include "exbii.mm"
include "exsimpr.mm"
include "syl.mm"
include "exlimiv.mm"
include "velsn.mm"
include "anbi2i.mm"
include "sylib.mm"
include "biimparc.mm"
include "vtoclga.mm"
include "wi.mm"
include "equid.mm"
include "wsb.mm"
include "eqid.mm"
include "wsbc.mm"
include "cvv.mm"
include "snex.mm"
include "sbcg.mm"
include "ax-mp.mm"
include "eqsbc3.mm"
include "adantl.mm"
include "biimpri.mm"
include "19.23bi.mm"
include "expcom.mm"
include "sylbir.mm"
include "sylbird.mm"
include "sbcth.mm"
include "sbcimg.mm"
include "mpbi.mm"
include "sbcan.mm"
include "wnf.mm"
include "nfv.mm"
include "nfab1.mm"
include "nfuni.mm"
include "nfcri.mm"
include "nfim.mm"
include "sbctt.mm"
include "mp2an.mm"
include "3imtr3i.mm"
include "syl2anbr.mm"
include "mpan2.mm"
include "syl5bir.mm"
include "mpbidi.mm"
include "com12.mm"
include "sbimi.mm"
include "equsb3.mm"
include "sbf.mm"
include "impbii.mm"
include "syl6bb.mm"
include "eqrdv.mm"
include "eqcomd.mm"

theorem mptsnunlem
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let vz: setvar z
  assume mptsnun.f: |- F = ( x e. A |-> { x } )
  assume mptsnun.r: |- R = { u | E. x e. A u = { x } }

  disjoint A u
  disjoint A x
  disjoint u x
  disjoint B u
  disjoint B x
  disjoint F x
  disjoint B z
  disjoint u z
  disjoint x z
  assert |- ( B C_ A -> B = U. ( F " B ) )

  proof
    cB
    cA
    wss
    #
    cF
    cB
    cima
    #
    cuni
    #
    cB
    @0
    vx
    @2
    cB
    @0
    vx
    cv
    #
    @2
    wcel
    @3
    vu
    cv
    #
    @3
    csn
    #
    wceq
    #
    vx
    cB
    wrex
    #
    vu
    cab
    #
    cuni
    #
    wcel
    #
    @3
    cB
    wcel
    #
    @0
    @2
    @9
    @3
    @0
    @1
    @8
    @0
    @1
    cF
    cB
    cres
    #
    crn
    #
    @8
    cF
    cB
    df-ima
    @0
    @13
    vx
    cB
    @5
    cmpt
    #
    crn
    @8
    @0
    @12
    @14
    @0
    @12
    vx
    cA
    @5
    cmpt
    #
    cB
    cres
    @14
    cF
    @15
    cB
    mptsnun.f
    reseq1i
    vx
    cA
    cB
    @5
    resmpt
    syl5eq
    rneqd
    vx
    vu
    cB
    rnmptsn
    syl6eq
    syl5eq
    unieqd
    eleq2d
    @10
    @11
    vz
    cv
    #
    cB
    wcel
    #
    @11
    vz
    @3
    @9
    @16
    @3
    cB
    eleq1
    #
    @16
    @9
    wcel
    #
    @11
    @16
    @3
    wceq
    #
    wa
    #
    vx
    wex
    #
    @17
    @19
    @11
    @16
    @5
    wcel
    #
    wa
    #
    vx
    wex
    #
    @22
    @19
    @16
    @4
    wcel
    #
    @7
    wa
    #
    vu
    wex
    #
    @25
    @7
    vu
    @16
    eluniab
    #
    @27
    @25
    vu
    @27
    @11
    @6
    @23
    wa
    #
    wa
    #
    vx
    wex
    #
    @25
    @27
    @11
    @6
    @26
    wa
    #
    wa
    #
    vx
    wex
    #
    @32
    @27
    @7
    @26
    wa
    @33
    vx
    cB
    wrex
    @35
    @26
    @7
    ancom
    @6
    @26
    vx
    cB
    r19.41v
    @33
    vx
    cB
    df-rex
    3bitr2i
    @34
    @31
    vx
    @33
    @30
    @11
    @33
    @30
    @6
    @33
    @30
    wb
    @26
    @6
    @26
    @23
    @6
    @4
    @5
    @16
    eleq2
    #
    anbi2d
    adantr
    ibi
    anim2i
    eximi
    sylbi
    @32
    @6
    @24
    wa
    #
    vx
    wex
    @25
    @31
    @37
    vx
    @11
    @6
    @23
    an12
    exbii
    @6
    @24
    vx
    exsimpr
    sylbi
    syl
    exlimiv
    sylbi
    @24
    @21
    vx
    @23
    @20
    @11
    vz
    @3
    velsn
    #
    anbi2i
    exbii
    sylib
    @21
    @17
    vx
    @20
    @17
    @11
    @18
    biimparc
    exlimiv
    syl
    vtoclga
    @3
    @3
    wceq
    #
    @11
    @10
    wi
    #
    vx
    equid
    @20
    vz
    vx
    wsb
    @40
    vz
    vx
    wsb
    @39
    @40
    @20
    @40
    vz
    vx
    @11
    @20
    @10
    @20
    @19
    @10
    @11
    @20
    @23
    @11
    @19
    @38
    @11
    @5
    @5
    wceq
    #
    @23
    @19
    wi
    #
    @5
    eqid
    @11
    @11
    vu
    @5
    wsbc
    #
    @6
    vu
    @5
    wsbc
    #
    @42
    @41
    @5
    cvv
    wcel
    #
    @43
    @11
    wb
    @3
    snex
    #
    @11
    vu
    @5
    cvv
    sbcg
    ax-mp
    @45
    @44
    @41
    wb
    @46
    vu
    @5
    @5
    cvv
    eqsbc3
    ax-mp
    @11
    @6
    wa
    #
    vu
    @5
    wsbc
    #
    @42
    vu
    @5
    wsbc
    #
    @43
    @44
    wa
    @42
    @47
    @42
    wi
    #
    vu
    @5
    wsbc
    #
    @48
    @49
    wi
    #
    @45
    @51
    @46
    @50
    vu
    @5
    cvv
    @47
    @23
    @26
    @19
    @6
    @26
    @23
    wb
    @11
    @36
    adantl
    @47
    @26
    @19
    wi
    #
    vx
    @47
    vx
    wex
    @7
    @53
    @6
    vx
    cB
    df-rex
    @26
    @7
    @19
    @27
    @19
    vu
    @19
    @28
    @29
    biimpri
    19.23bi
    expcom
    sylbir
    19.23bi
    sylbird
    sbcth
    ax-mp
    @45
    @51
    @52
    wb
    @46
    @47
    @42
    vu
    @5
    cvv
    sbcimg
    ax-mp
    mpbi
    @11
    @6
    vu
    @5
    sbcan
    @45
    @42
    vu
    wnf
    @49
    @42
    wb
    @46
    @23
    @19
    vu
    @23
    vu
    nfv
    vu
    vz
    @9
    vu
    @8
    @7
    vu
    nfab1
    nfuni
    nfcri
    nfim
    @42
    vu
    @5
    cvv
    sbctt
    mp2an
    3imtr3i
    syl2anbr
    mpan2
    syl5bir
    @16
    @3
    @9
    eleq1
    mpbidi
    com12
    sbimi
    vx
    vz
    vx
    equsb3
    @40
    vz
    vx
    @40
    vz
    nfv
    sbf
    3imtr3i
    ax-mp
    impbii
    syl6bb
    eqrdv
    eqcomd
end
