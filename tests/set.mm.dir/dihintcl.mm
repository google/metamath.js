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
include "cbs.mm"
include "eqid.mm"
include "dihfn.mm"
include "dihdm.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "adantr.mm"
include "cnvimass.mm"
include "fnssres.mm"
include "sylancl.mm"
include "fniinfv.mm"
include "syl.mm"
include "df-ima.mm"
include "wfo.mm"
include "dffn4.mm"
include "sylib.mm"
include "simprl.mm"
include "foimacnv.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "inteqd.mm"
include "eqtrd.mm"
include "cglb.mm"
include "simpl.mm"
include "syl5sseq.mm"
include "wex.mm"
include "simprr.mm"
include "n0.mm"
include "wrex.mm"
include "sselda.mm"
include "wb.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "wi.mm"
include "wfun.mm"
include "fnfun.mm"
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
include "dihglb.mm"
include "syl12anc.mm"
include "fvres.mm"
include "iineq2i.mm"
include "syl6eqr.mm"
include "ccla.mm"
include "hlclat.mm"
include "ad2antrr.mm"
include "clatglbcl.mm"
include "dihcl.mm"
include "syldan.mm"
include "eqeltrrd.mm"

theorem dihintcl
  let cS: class S
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume dihintcl.h: |- H = ( LHyp ` K )
  assume dihintcl.i: |- I = ( ( DIsoH ` K ) ` W )


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
    @16
    @2
    @18
    @6
    @2
    @18
    cI
    cK
    cbs
    cfv
    #
    wfn
    #
    @19
    cH
    cI
    cK
    cW
    @19
    eqid
    #
    dihintcl.h
    dihintcl.i
    dihfn
    #
    @2
    @17
    @19
    cI
    @19
    cH
    cI
    cK
    cW
    @21
    dihintcl.h
    dihintcl.i
    dihdm
    #
    fneq2d
    mpbird
    adantr
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
    @19
    @3
    cI
    wfo
    #
    @4
    @25
    cS
    wceq
    @7
    @20
    @26
    @2
    @20
    @6
    @22
    adantr
    #
    @19
    cI
    dffn4
    sylib
    @2
    @4
    @5
    simprl
    #
    @19
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
    @31
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
    @8
    @19
    wss
    #
    @8
    c0
    wne
    #
    @31
    @33
    wceq
    @2
    @6
    simpl
    @7
    @17
    @8
    @19
    @24
    @2
    @17
    @19
    wceq
    @6
    @23
    adantr
    #
    syl5sseq
    #
    @7
    @9
    cS
    wcel
    #
    @35
    vy
    @7
    @5
    @38
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
    @38
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
    @35
    @39
    @9
    @3
    wcel
    #
    @43
    @7
    cS
    @3
    @9
    @28
    sselda
    @39
    @18
    @44
    @43
    wb
    @7
    @18
    @38
    @7
    @18
    @20
    @27
    @7
    @17
    @19
    cI
    @36
    fneq2d
    mpbird
    adantr
    vx
    @17
    @9
    cI
    fvelrnb
    syl
    mpbid
    @39
    @42
    @35
    vx
    @17
    @7
    @38
    @40
    @17
    wcel
    #
    @42
    @35
    wi
    wi
    @7
    @42
    @45
    @38
    @35
    @7
    @45
    @41
    cS
    wcel
    #
    @35
    wi
    #
    @42
    @38
    @35
    wi
    @7
    @45
    @47
    @7
    @45
    wa
    @46
    @40
    @8
    wcel
    #
    @35
    @7
    cI
    wfun
    #
    @45
    @46
    @48
    wb
    @7
    @20
    @49
    @27
    @19
    cI
    fnfun
    syl
    @40
    cS
    cI
    fvimacnv
    sylan
    @8
    @40
    ne0i
    syl6bi
    ex
    @42
    @38
    @46
    @35
    @42
    @46
    @38
    @41
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
    vy
    @19
    @8
    @29
    cH
    cI
    cK
    cW
    @21
    @29
    eqid
    #
    dihintcl.h
    dihintcl.i
    dihglb
    syl12anc
    vy
    @8
    @11
    @32
    @9
    @8
    cI
    fvres
    iineq2i
    syl6eqr
    @2
    @6
    @30
    @19
    wcel
    #
    @31
    @3
    wcel
    @7
    cK
    ccla
    wcel
    #
    @34
    @51
    @0
    @52
    @1
    @6
    cK
    hlclat
    ad2antrr
    @37
    @19
    @8
    @29
    cK
    @21
    @50
    clatglbcl
    syl2anc
    @19
    cH
    cI
    cK
    cW
    @30
    @21
    dihintcl.h
    dihintcl.i
    dihcl
    syldan
    eqeltrrd
    eqeltrrd
end
