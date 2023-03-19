include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "cres.mm"
include "cfv.mm"
include "ciin.mm"
include "cint.mm"
include "wfn.mm"
include "wceq.mm"
include "cdm.mm"
include "wf1o.mm"
include "diaf11N.mm"
include "adantr.mm"
include "f1ofn.mm"
include "syl.mm"
include "cnvimass.mm"
include "fnssres.mm"
include "sylancl.mm"
include "fniinfv.mm"
include "df-ima.mm"
include "wfo.mm"
include "f1ofo.mm"
include "simprl.mm"
include "foimacnv.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "inteqd.mm"
include "eqtrd.mm"
include "cglb.mm"
include "simpl.mm"
include "a1i.mm"
include "wex.mm"
include "simprr.mm"
include "n0.mm"
include "sylib.mm"
include "wrex.mm"
include "sselda.mm"
include "wb.mm"
include "ad2antrr.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "wi.mm"
include "wfun.mm"
include "f1ofun.mm"
include "fvimacnv.mm"
include "sylan.mm"
include "ne0i.mm"
include "syl6bi.mm"
include "ex.mm"
include "eleq1.mm"
include "biimprd.mm"
include "imim1d.mm"
include "syl9.mm"
include "com24.mm"
include "imp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "exlimddv.mm"
include "eqid.mm"
include "diaglbN.mm"
include "syl12anc.mm"
include "fvres.mm"
include "iineq2i.mm"
include "syl6eqr.mm"
include "cbs.mm"
include "cple.mm"
include "wbr.mm"
include "ccla.mm"
include "hlclat.mm"
include "crab.mm"
include "diadm.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "syl5ss.mm"
include "clatglbcl.mm"
include "clat.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "lhpbase.mm"
include "ad3antlr.mm"
include "syl5sseq.mm"
include "syl6ss.mm"
include "simpr.mm"
include "clatglble.mm"
include "syl3anc.mm"
include "sseli.mm"
include "adantl.mm"
include "diaeldm.mm"
include "simprd.mm"
include "lattrd.mm"
include "mpbir2and.mm"
include "diaclN.mm"
include "syldan.mm"
include "eqeltrrd.mm"

theorem diaintclN
  let cS: class S
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume diaintcl.h: |- H = ( LHyp ` K )
  assume diaintcl.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ ran I /\ S =/= (/) ) ) -> |^| S e. ran I )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cS
    cI
    crn
    #
    wss
    #
    cS
    c0
    wne
    #
    wa
    #
    wa
    #
    vy
    cI
    ccnv
    cS
    cima
    #
    vy
    cv
    #
    cI
    @8
    cres
    #
    cfv
    #
    ciin
    #
    cS
    cint
    #
    @3
    @7
    @12
    @10
    crn
    #
    cint
    #
    @13
    @7
    @10
    @8
    wfn
    #
    @12
    @15
    wceq
    @7
    cI
    cI
    cdm
    #
    wfn
    #
    @8
    @17
    wss
    #
    @16
    @7
    @17
    @3
    cI
    wf1o
    #
    @18
    @2
    @20
    @6
    cH
    cI
    cK
    cW
    diaintcl.h
    diaintcl.i
    diaf11N
    #
    adantr
    @17
    @3
    cI
    f1ofn
    #
    syl
    cI
    cS
    cnvimass
    #
    @17
    @8
    cI
    fnssres
    sylancl
    vy
    @8
    @10
    fniinfv
    syl
    @7
    @14
    cS
    @7
    @14
    cI
    @8
    cima
    #
    cS
    cI
    @8
    df-ima
    @7
    @17
    @3
    cI
    wfo
    #
    @4
    @24
    cS
    wceq
    @2
    @25
    @6
    @2
    @20
    @25
    @21
    @17
    @3
    cI
    f1ofo
    syl
    adantr
    @2
    @4
    @5
    simprl
    #
    @17
    @3
    cS
    cI
    foimacnv
    syl2anc
    syl5eqr
    inteqd
    eqtrd
    @7
    @8
    cK
    cglb
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    @12
    @3
    @7
    @29
    vy
    @8
    @9
    cI
    cfv
    #
    ciin
    #
    @12
    @7
    @2
    @19
    @8
    c0
    wne
    #
    @29
    @31
    wceq
    @2
    @6
    simpl
    @19
    @7
    @23
    a1i
    @7
    @9
    cS
    wcel
    #
    @32
    vy
    @7
    @5
    @33
    vy
    wex
    @2
    @4
    @5
    simprr
    vy
    cS
    n0
    sylib
    @7
    @33
    wa
    #
    vx
    cv
    #
    cI
    cfv
    #
    @9
    wceq
    #
    vx
    @17
    wrex
    #
    @32
    @34
    @9
    @3
    wcel
    #
    @38
    @7
    cS
    @3
    @9
    @26
    sselda
    @34
    @18
    @39
    @38
    wb
    @34
    @20
    @18
    @2
    @20
    @6
    @33
    @21
    ad2antrr
    @22
    syl
    vx
    @17
    @9
    cI
    fvelrnb
    syl
    mpbid
    @34
    @37
    @32
    vx
    @17
    @7
    @33
    @35
    @17
    wcel
    #
    @37
    @32
    wi
    wi
    @7
    @37
    @40
    @33
    @32
    @7
    @40
    @36
    cS
    wcel
    #
    @32
    wi
    #
    @37
    @33
    @32
    wi
    @7
    @40
    @42
    @7
    @40
    wa
    @41
    @35
    @8
    wcel
    #
    @32
    @7
    cI
    wfun
    #
    @40
    @41
    @43
    wb
    @2
    @44
    @6
    @2
    @20
    @44
    @21
    @17
    @3
    cI
    f1ofun
    syl
    adantr
    @35
    cS
    cI
    fvimacnv
    sylan
    @8
    @35
    ne0i
    syl6bi
    ex
    @37
    @33
    @41
    @32
    @37
    @41
    @33
    @36
    @9
    cS
    eleq1
    biimprd
    imim1d
    syl9
    com24
    imp
    rexlimdv
    mpd
    exlimddv
    #
    vy
    @8
    @27
    cH
    cI
    cK
    cW
    @27
    eqid
    #
    diaintcl.h
    diaintcl.i
    diaglbN
    syl12anc
    vy
    @8
    @11
    @30
    @9
    @8
    cI
    fvres
    iineq2i
    syl6eqr
    @2
    @6
    @28
    @17
    wcel
    #
    @29
    @3
    wcel
    @7
    @47
    @28
    cK
    cbs
    cfv
    #
    wcel
    #
    @28
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @7
    cK
    ccla
    wcel
    #
    @8
    @48
    wss
    #
    @49
    @0
    @52
    @1
    @6
    cK
    hlclat
    #
    ad2antrr
    @7
    @8
    @17
    @48
    @23
    @2
    @17
    @48
    wss
    @6
    @2
    @17
    @35
    cW
    @50
    wbr
    #
    vx
    @48
    crab
    #
    @48
    vx
    @48
    cH
    cI
    cK
    @50
    chlt
    cW
    @48
    eqid
    #
    @50
    eqid
    #
    diaintcl.h
    diaintcl.i
    diadm
    #
    @55
    vx
    @48
    ssrab2
    #
    syl6eqss
    adantr
    syl5ss
    #
    @48
    @8
    @27
    cK
    @57
    @46
    clatglbcl
    syl2anc
    #
    @7
    @9
    @8
    wcel
    #
    @51
    vy
    @7
    @32
    @63
    vy
    wex
    @45
    vy
    @8
    n0
    sylib
    @7
    @63
    wa
    #
    @48
    cK
    @50
    @28
    @9
    cW
    @57
    @58
    @0
    cK
    clat
    wcel
    @1
    @6
    @63
    cK
    hllat
    ad3antrrr
    @7
    @49
    @63
    @62
    adantr
    @7
    @8
    @48
    @9
    @61
    sselda
    @1
    cW
    @48
    wcel
    @0
    @6
    @63
    @48
    cH
    cK
    cW
    @57
    diaintcl.h
    lhpbase
    ad3antlr
    @64
    @52
    @53
    @63
    @28
    @9
    @50
    wbr
    @0
    @52
    @1
    @6
    @63
    @54
    ad3antrrr
    @7
    @53
    @63
    @7
    @8
    @56
    @48
    @7
    @17
    @8
    @56
    @23
    @2
    @17
    @56
    wceq
    @6
    @59
    adantr
    syl5sseq
    @60
    syl6ss
    adantr
    @7
    @63
    simpr
    @48
    @8
    @27
    cK
    @50
    @9
    @57
    @58
    @46
    clatglble
    syl3anc
    @64
    @9
    @48
    wcel
    #
    @9
    cW
    @50
    wbr
    #
    @64
    @9
    @17
    wcel
    #
    @65
    @66
    wa
    #
    @63
    @67
    @7
    @8
    @17
    @9
    @23
    sseli
    adantl
    @2
    @67
    @68
    wb
    @6
    @63
    @48
    cH
    cI
    cK
    @50
    chlt
    cW
    @9
    @57
    @58
    diaintcl.h
    diaintcl.i
    diaeldm
    ad2antrr
    mpbid
    simprd
    lattrd
    exlimddv
    @2
    @47
    @49
    @51
    wa
    wb
    @6
    @48
    cH
    cI
    cK
    @50
    chlt
    cW
    @28
    @57
    @58
    diaintcl.h
    diaintcl.i
    diaeldm
    adantr
    mpbir2and
    cH
    cI
    cK
    cW
    @28
    diaintcl.h
    diaintcl.i
    diaclN
    syldan
    eqeltrrd
    eqeltrrd
end
