include "cv.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "snex.mm"
include "a1i.mm"
include "syl.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "wa.mm"
include "wex.mm"
include "crn.mm"
include "wbr.mm"
include "weu.mm"
include "wfn.mm"
include "wi.mm"
include "ffn.mm"
include "imp.mm"
include "snidg.mm"
include "adantr.mm"
include "fneu.mm"
include "cab.mm"
include "euabsn.mm"
include "cima.mm"
include "wrel.mm"
include "frel.mm"
include "relimasn.mm"
include "cdm.mm"
include "imadmrn.mm"
include "fdm.mm"
include "imaeq2d.mm"
include "syl5reqr.mm"
include "eqtr3d.mm"
include "eqeq1d.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "adantl.mm"
include "mpbid.mm"
include "vex.mm"
include "snid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "frn.mm"
include "sseld.mm"
include "syl5.mm"
include "adantll.mm"
include "wfo.mm"
include "dffn4.mm"
include "sylib.mm"
include "fof.mm"
include "feq3.mm"
include "syl5ibcom.mm"
include "ad2antrr.mm"
include "fsng.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "w3a.mm"
include "wss.mm"
include "wf1o.mm"
include "f1osng.mm"
include "f1oeq1.mm"
include "bicomd.mm"
include "f1of.mm"
include "3adant2.mm"
include "snssi.mm"
include "3ad2ant2.mm"
include "fss.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "bitrd.mm"
include "abbi2dv.mm"

theorem mapsnd
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cV: class V
  let cW: class W
  assume mapsnd.1: |- ( ph -> A e. V )
  assume mapsnd.2: |- ( ph -> B e. W )

  disjoint A f
  disjoint A y
  disjoint f y
  disjoint B f
  disjoint B y
  disjoint f ph
  disjoint ph y
  assert |- ( ph -> ( A ^m { B } ) = { f | E. y e. A f = { <. B , y >. } } )

  proof
    wph
    vf
    cv
    #
    cB
    vy
    cv
    #
    cop
    csn
    #
    wceq
    #
    vy
    cA
    wrex
    #
    vf
    cA
    cB
    csn
    #
    cmap
    co
    #
    wph
    @0
    @6
    wcel
    #
    @5
    cA
    @0
    wf
    #
    @4
    wph
    cA
    cV
    wcel
    @5
    cvv
    wcel
    #
    @7
    @8
    wb
    mapsnd.1
    wph
    cB
    cW
    wcel
    #
    @9
    mapsnd.2
    @9
    @10
    cB
    snex
    a1i
    syl
    cA
    @5
    @0
    cV
    cvv
    elmapg
    syl2anc
    wph
    @8
    @4
    wph
    @8
    @4
    wph
    @8
    wa
    #
    @1
    cA
    wcel
    #
    @3
    wa
    #
    vy
    wex
    #
    @4
    @11
    @0
    crn
    #
    @1
    csn
    #
    wceq
    #
    vy
    wex
    #
    @14
    @11
    cB
    @1
    @0
    wbr
    #
    vy
    weu
    #
    @18
    @11
    @0
    @5
    wfn
    #
    cB
    @5
    wcel
    #
    @20
    wph
    @8
    @21
    @8
    @21
    wi
    wph
    @5
    cA
    @0
    ffn
    #
    a1i
    imp
    wph
    @22
    @8
    wph
    @10
    @22
    mapsnd.2
    cB
    cW
    snidg
    syl
    adantr
    vy
    @5
    cB
    @0
    fneu
    syl2anc
    @8
    @20
    @18
    wb
    wph
    @20
    @19
    vy
    cab
    #
    @16
    wceq
    #
    vy
    wex
    @8
    @18
    @19
    vy
    euabsn
    @8
    @25
    @17
    vy
    @8
    @24
    @15
    @16
    @8
    @0
    @5
    cima
    #
    @24
    @15
    @8
    @0
    wrel
    @26
    @24
    wceq
    @5
    cA
    @0
    frel
    vy
    cB
    @0
    relimasn
    syl
    @8
    @15
    @0
    @0
    cdm
    #
    cima
    @26
    @0
    imadmrn
    @8
    @27
    @5
    @0
    @5
    cA
    @0
    fdm
    imaeq2d
    syl5reqr
    eqtr3d
    eqeq1d
    exbidv
    syl5bb
    adantl
    mpbid
    @11
    @17
    @13
    vy
    @11
    @17
    @13
    @11
    @17
    wa
    #
    @12
    @3
    @8
    @17
    @12
    wph
    @8
    @17
    @12
    @17
    @1
    @15
    wcel
    #
    @8
    @12
    @17
    @29
    @1
    @16
    wcel
    @1
    vy
    vex
    #
    snid
    @15
    @16
    @1
    eleq2
    mpbiri
    @8
    @15
    cA
    @1
    @5
    cA
    @0
    frn
    sseld
    syl5
    imp
    adantll
    @28
    @5
    @16
    @0
    wf
    #
    @3
    @8
    @17
    @31
    wph
    @8
    @17
    @31
    @8
    @5
    @15
    @0
    wf
    #
    @17
    @31
    @8
    @5
    @15
    @0
    wfo
    #
    @32
    @8
    @21
    @33
    @23
    @5
    @0
    dffn4
    sylib
    @5
    @15
    @0
    fof
    syl
    @15
    @16
    @5
    @0
    feq3
    syl5ibcom
    imp
    adantll
    @28
    @10
    @1
    cvv
    wcel
    #
    @31
    @3
    wb
    wph
    @10
    @8
    @17
    mapsnd.2
    ad2antrr
    @34
    @28
    @30
    a1i
    cB
    @1
    cW
    cvv
    @0
    fsng
    syl2anc
    mpbid
    jca
    ex
    eximdv
    mpd
    @3
    vy
    cA
    df-rex
    sylibr
    ex
    wph
    @3
    @8
    vy
    cA
    wph
    @12
    @3
    @8
    wph
    @12
    @3
    w3a
    @31
    @16
    cA
    wss
    #
    @8
    wph
    @3
    @31
    @12
    wph
    @3
    wa
    #
    @5
    @16
    @0
    wf1o
    #
    @31
    @36
    @5
    @16
    @2
    wf1o
    #
    @37
    wph
    @38
    @3
    wph
    @10
    @34
    @38
    mapsnd.2
    @34
    wph
    @30
    a1i
    cB
    @1
    cW
    cvv
    f1osng
    syl2anc
    adantr
    @3
    @38
    @37
    wb
    wph
    @3
    @37
    @38
    @5
    @16
    @0
    @2
    f1oeq1
    bicomd
    adantl
    mpbid
    @5
    @16
    @0
    f1of
    syl
    3adant2
    @12
    wph
    @35
    @3
    @1
    cA
    snssi
    3ad2ant2
    @5
    @16
    cA
    @0
    fss
    syl2anc
    3exp
    rexlimdv
    impbid
    bitrd
    abbi2dv
end
