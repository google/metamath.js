include "wac.mm"
include "cv.mm"
include "cdm.mm"
include "ccmp.mm"
include "wf.mm"
include "cpt.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cvv.mm"
include "cuni.mm"
include "cufl.mm"
include "ccrd.mm"
include "cin.mm"
include "vex.mm"
include "dmex.mm"
include "a1i.mm"
include "simpr.mm"
include "fvex.mm"
include "uniex.mm"
include "wceq.mm"
include "acufl.mm"
include "adantr.mm"
include "syl5eleqr.mm"
include "simpl.mm"
include "dfac10.mm"
include "sylib.mm"
include "elind.mm"
include "eqid.mm"
include "ptcmpg.mm"
include "syl3anc.mm"
include "ex.mm"
include "alrimiv.mm"
include "wfun.mm"
include "c0.mm"
include "crn.mm"
include "wnel.mm"
include "cixp.mm"
include "wne.mm"
include "cpw.mm"
include "csn.mm"
include "cpr.mm"
include "ctg.mm"
include "cmpt.mm"
include "wss.mm"
include "kelac2lem.mm"
include "mp1i.mm"
include "fmptd.mm"
include "ffdm.mm"
include "syl.mm"
include "simpld.mm"
include "mptex.mm"
include "id.mm"
include "dmeq.mm"
include "feq12d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "spcv.mm"
include "syl5com.mm"
include "wn.mm"
include "df-nel.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "fvelrn.mm"
include "adantlr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "unieqd.mm"
include "pweqd.mm"
include "sneqd.mm"
include "preq12d.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "fveq2i.mm"
include "eleq1i.mm"
include "adantl.mm"
include "kelac2.mm"
include "syldc.mm"
include "dfac9.mm"
include "sylibr.mm"
include "impbii.mm"

theorem dfac21
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vx: setvar x


  assert |- ( CHOICE <-> A. f ( f : dom f --> Comp -> ( Xt_ ` f ) e. Comp ) )

  proof
    wac
    vf
    cv
    #
    cdm
    #
    ccmp
    @0
    wf
    #
    @0
    cpt
    cfv
    #
    ccmp
    wcel
    #
    wi
    #
    vf
    wal
    #
    wac
    @5
    vf
    wac
    @2
    @4
    wac
    @2
    wa
    #
    @1
    cvv
    wcel
    #
    @2
    @3
    cuni
    #
    cufl
    ccrd
    cdm
    #
    cin
    wcel
    @4
    @8
    @7
    @0
    vf
    vex
    dmex
    a1i
    wac
    @2
    simpr
    @7
    cufl
    @10
    @9
    @7
    @9
    cvv
    cufl
    @3
    @0
    cpt
    fvex
    uniex
    #
    wac
    cufl
    cvv
    wceq
    @2
    acufl
    adantr
    syl5eleqr
    @7
    @9
    cvv
    @10
    @11
    @7
    wac
    @10
    cvv
    wceq
    wac
    @2
    simpl
    dfac10
    sylib
    syl5eleqr
    elind
    @1
    @0
    @3
    cvv
    @9
    @3
    eqid
    @9
    eqid
    ptcmpg
    syl3anc
    ex
    alrimiv
    @6
    vg
    cv
    #
    wfun
    #
    c0
    @12
    crn
    #
    wnel
    #
    wa
    #
    vx
    @12
    cdm
    #
    vx
    cv
    #
    @12
    cfv
    #
    cixp
    c0
    wne
    #
    wi
    #
    vg
    wal
    wac
    @6
    @21
    vg
    @16
    @6
    vy
    @17
    vy
    cv
    #
    @12
    cfv
    #
    @23
    cuni
    #
    cpw
    #
    csn
    #
    cpr
    #
    ctg
    cfv
    #
    cmpt
    #
    cpt
    cfv
    #
    ccmp
    wcel
    #
    @20
    @16
    @29
    cdm
    #
    ccmp
    @29
    wf
    #
    @6
    @31
    @16
    @33
    @32
    @17
    wss
    #
    @16
    @17
    ccmp
    @29
    wf
    @33
    @34
    wa
    @16
    vy
    @17
    @28
    ccmp
    @29
    @23
    cvv
    wcel
    @28
    ccmp
    wcel
    @16
    @22
    @17
    wcel
    wa
    @22
    @12
    fvex
    @23
    cvv
    kelac2lem
    mp1i
    @29
    eqid
    fmptd
    @17
    ccmp
    @29
    ffdm
    syl
    simpld
    @5
    @33
    @31
    wi
    vf
    @29
    vy
    @17
    @28
    @12
    vg
    vex
    dmex
    mptex
    @0
    @29
    wceq
    #
    @2
    @33
    @4
    @31
    @35
    @1
    @32
    ccmp
    @0
    @29
    @35
    id
    @0
    @29
    dmeq
    feq12d
    @35
    @3
    @30
    ccmp
    @0
    @29
    cpt
    fveq2
    eleq1d
    imbi12d
    spcv
    syl5com
    @16
    @31
    @20
    @16
    @31
    wa
    #
    vx
    @19
    @17
    cvv
    @19
    cvv
    wcel
    @36
    @18
    @17
    wcel
    #
    wa
    @18
    @12
    fvex
    a1i
    @16
    @37
    @19
    c0
    wne
    #
    @31
    @16
    @37
    wa
    #
    c0
    @14
    wcel
    #
    wn
    #
    @38
    @15
    @41
    @13
    @37
    @15
    @41
    c0
    @14
    df-nel
    biimpi
    ad2antlr
    @39
    @40
    @19
    c0
    @39
    @19
    @14
    wcel
    #
    @19
    c0
    wceq
    @40
    @13
    @37
    @42
    @15
    @18
    @12
    fvelrn
    adantlr
    @19
    c0
    @14
    eleq1
    syl5ibcom
    necon3bd
    mpd
    adantlr
    @31
    vx
    @17
    @19
    @19
    cuni
    #
    cpw
    #
    csn
    #
    cpr
    #
    ctg
    cfv
    #
    cmpt
    #
    cpt
    cfv
    #
    ccmp
    wcel
    #
    @16
    @31
    @50
    @30
    @49
    ccmp
    @29
    @48
    cpt
    vy
    vx
    @17
    @28
    @47
    @22
    @18
    wceq
    #
    @27
    @46
    ctg
    @51
    @23
    @19
    @26
    @45
    @22
    @18
    @12
    fveq2
    #
    @51
    @25
    @44
    @51
    @24
    @43
    @51
    @23
    @19
    @52
    unieqd
    pweqd
    sneqd
    preq12d
    fveq2d
    cbvmptv
    fveq2i
    eleq1i
    biimpi
    adantl
    kelac2
    ex
    syldc
    alrimiv
    vx
    vg
    dfac9
    sylibr
    impbii
end
