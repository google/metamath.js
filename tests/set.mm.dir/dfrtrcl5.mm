include "crtcl.mm"
include "cvv.mm"
include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wss.mm"
include "ccom.mm"
include "w3a.mm"
include "cab.mm"
include "cint.mm"
include "cmpt.mm"
include "wa.mm"
include "df-rtrcl.mm"
include "ancom.mm"
include "anbi2i.mm"
include "abbii.mm"
include "inteqi.mm"
include "mpteq2i.mm"
include "wcel.mm"
include "vex.mm"
include "rtrclexi.mm"
include "a1i.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "resiexg.mm"
include "mp2b.mm"
include "unex.mm"
include "trclexi.mm"
include "simpr.mm"
include "cotrintab.mm"
include "wceq.mm"
include "dmex.mm"
include "rnex.mm"
include "resiexd.mm"
include "mp2an.mm"
include "dmtrcl.mm"
include "ax-mp.mm"
include "dmun.mm"
include "dmresi.mm"
include "uneq2i.mm"
include "ssun1.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "3eqtri.mm"
include "eqtri.mm"
include "rntrcl.mm"
include "rnun.mm"
include "rnresi.mm"
include "ssun2.mm"
include "uneq12i.mm"
include "unidm.mm"
include "reseq2i.mm"
include "ssmin.mm"
include "sstri.mm"
include "eqsstri.mm"
include "simprl.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "mptrcllem.mm"
include "df-3an.mm"
include "unss.mm"
include "bitri.mm"
include "anbi1i.mm"
include "bitr2i.mm"
include "eqtr4i.mm"

theorem dfrtrcl5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- t* = ( x e. _V |-> |^| { y | ( x C_ y /\ ( ( _I |` ( dom y u. ran y ) ) C_ y /\ ( y o. y ) C_ y ) ) } )

  proof
    crtcl
    vx
    cvv
    cid
    vx
    cv
    #
    cdm
    #
    @0
    crn
    #
    cun
    #
    cres
    #
    vz
    cv
    #
    wss
    #
    @0
    @5
    wss
    #
    @5
    @5
    ccom
    #
    @5
    wss
    #
    w3a
    #
    vz
    cab
    #
    cint
    #
    cmpt
    #
    vx
    cvv
    @0
    vy
    cv
    #
    wss
    #
    cid
    @14
    cdm
    #
    @14
    crn
    #
    cun
    #
    cres
    #
    @14
    wss
    #
    @14
    @14
    ccom
    #
    @14
    wss
    #
    wa
    #
    wa
    #
    vy
    cab
    #
    cint
    #
    cmpt
    #
    vx
    vz
    df-rtrcl
    @27
    vx
    cvv
    @15
    @22
    @20
    wa
    #
    wa
    #
    vy
    cab
    #
    cint
    #
    cmpt
    vx
    cvv
    @0
    @4
    cun
    #
    @5
    wss
    #
    @9
    wa
    #
    vz
    cab
    #
    cint
    #
    cmpt
    @13
    vx
    cvv
    @26
    @31
    @25
    @30
    @24
    @29
    vy
    @23
    @28
    @15
    @20
    @22
    ancom
    anbi2i
    abbii
    inteqi
    mpteq2i
    @22
    @9
    @36
    @36
    ccom
    #
    @36
    wss
    #
    cid
    @36
    cdm
    #
    @36
    crn
    #
    cun
    #
    cres
    #
    @36
    wss
    #
    @31
    @31
    ccom
    #
    @31
    wss
    #
    vx
    vy
    vz
    cvv
    @31
    cvv
    wcel
    @0
    cvv
    wcel
    #
    vy
    @0
    cvv
    vx
    vex
    #
    rtrclexi
    a1i
    @36
    cvv
    wcel
    @46
    vz
    @32
    cvv
    @0
    @4
    @47
    @46
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    @47
    @46
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    @48
    @0
    cvv
    dmexg
    @0
    cvv
    rnexg
    @1
    @2
    cvv
    cvv
    unexg
    #
    syl2anc
    @3
    cvv
    resiexg
    mp2b
    unex
    trclexi
    a1i
    @38
    @46
    @34
    vz
    @33
    @9
    simpr
    cotrintab
    a1i
    @43
    @46
    @42
    @4
    @36
    @41
    @3
    cid
    @41
    @3
    @3
    cun
    @3
    @39
    @3
    @40
    @3
    @39
    @32
    cdm
    #
    @3
    @32
    cvv
    wcel
    #
    @39
    @53
    wceq
    @0
    @4
    @47
    @50
    @51
    @49
    @0
    @47
    dmex
    @0
    @47
    rnex
    @50
    @51
    wa
    @3
    cvv
    @52
    resiexd
    mp2an
    unex
    #
    vz
    cvv
    @32
    dmtrcl
    ax-mp
    @53
    @1
    @4
    cdm
    #
    cun
    @1
    @3
    cun
    #
    @3
    @0
    @4
    dmun
    @56
    @3
    @1
    @3
    dmresi
    uneq2i
    @1
    @3
    wss
    @57
    @3
    wceq
    @1
    @2
    ssun1
    @1
    @3
    ssequn1
    mpbi
    3eqtri
    eqtri
    @40
    @32
    crn
    #
    @3
    @54
    @40
    @58
    wceq
    @55
    vz
    cvv
    @32
    rntrcl
    ax-mp
    @58
    @2
    @4
    crn
    #
    cun
    @2
    @3
    cun
    #
    @3
    @0
    @4
    rnun
    @59
    @3
    @2
    @3
    rnresi
    uneq2i
    @2
    @3
    wss
    @60
    @3
    wceq
    @2
    @1
    ssun2
    @2
    @3
    ssequn1
    mpbi
    3eqtri
    eqtri
    uneq12i
    @3
    unidm
    eqtri
    reseq2i
    @4
    @32
    @36
    @4
    @0
    ssun2
    @9
    vz
    @32
    ssmin
    sstri
    eqsstri
    a1i
    @45
    @46
    @29
    vy
    @15
    @22
    @20
    simprl
    cotrintab
    a1i
    @14
    @36
    wceq
    #
    @21
    @37
    @14
    @36
    @61
    @14
    @36
    @14
    @36
    @61
    id
    #
    @62
    coeq12d
    @62
    sseq12d
    @61
    @19
    @42
    @14
    @36
    @61
    @18
    @41
    cid
    @61
    @16
    @39
    @17
    @40
    @14
    @36
    dmeq
    @14
    @36
    rneq
    uneq12d
    reseq2d
    @62
    sseq12d
    @5
    @31
    wceq
    #
    @8
    @44
    @5
    @31
    @63
    @5
    @31
    @5
    @31
    @63
    id
    #
    @64
    coeq12d
    @64
    sseq12d
    mptrcllem
    vx
    cvv
    @36
    @12
    @35
    @11
    @34
    @10
    vz
    @10
    @6
    @7
    wa
    #
    @9
    wa
    @34
    @6
    @7
    @9
    df-3an
    @65
    @33
    @9
    @65
    @7
    @6
    wa
    @33
    @6
    @7
    ancom
    @0
    @4
    @5
    unss
    bitri
    anbi1i
    bitr2i
    abbii
    inteqi
    mpteq2i
    3eqtri
    eqtr4i
end
