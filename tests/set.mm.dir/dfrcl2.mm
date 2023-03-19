include "crcl.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cmpt.mm"
include "df-rcl.mm"
include "wcel.mm"
include "crab.mm"
include "wceq.mm"
include "rabab.mm"
include "eqcomi.mm"
include "inteqi.mm"
include "a1i.mm"
include "vex.mm"
include "dmex.mm"
include "rnex.mm"
include "unex.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "ssun2.mm"
include "dmun.mm"
include "dmresi.mm"
include "uneq1i.mm"
include "un23.mm"
include "unidm.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "rnun.mm"
include "rnresi.mm"
include "unass.mm"
include "uneq2i.mm"
include "uneq12i.mm"
include "reseq2i.mm"
include "ssun1.mm"
include "eqsstri.mm"
include "pm3.2i.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "cleq2lem.mm"
include "intminss.mm"
include "sylancl.mm"
include "eqsstrd.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "dmss.mm"
include "rnss.mm"
include "unss12.mm"
include "syl2anc.mm"
include "dfss.mm"
include "sylib.mm"
include "incom.mm"
include "syl6eq.mm"
include "resres.mm"
include "syl6eqr.mm"
include "resss.mm"
include "adantr.mm"
include "simpr.mm"
include "sstrd.mm"
include "simpl.mm"
include "unssd.mm"
include "ax-gen.mm"
include "ssintab.mm"
include "sylibr.mm"
include "eqssd.mm"
include "mpteq2ia.mm"

theorem dfrcl2
  let vx: setvar x
  let vz: setvar z


  assert |- r* = ( x e. _V |-> ( ( _I |` ( dom x u. ran x ) ) u. x ) )

  proof
    crcl
    vx
    cvv
    vx
    cv
    #
    vz
    cv
    #
    wss
    #
    cid
    @1
    cdm
    #
    @1
    crn
    #
    cun
    #
    cres
    #
    @1
    wss
    #
    wa
    #
    vz
    cab
    #
    cint
    #
    cmpt
    vx
    cvv
    cid
    @0
    cdm
    #
    @0
    crn
    #
    cun
    #
    cres
    #
    @0
    cun
    #
    cmpt
    vx
    vz
    df-rcl
    vx
    cvv
    @10
    @15
    @0
    cvv
    wcel
    #
    @10
    @15
    @16
    @10
    @8
    vz
    cvv
    crab
    #
    cint
    #
    @15
    @10
    @18
    wceq
    @16
    @9
    @17
    @17
    @9
    @8
    vz
    rabab
    eqcomi
    inteqi
    a1i
    @16
    @15
    cvv
    wcel
    #
    @0
    @15
    wss
    #
    cid
    @15
    cdm
    #
    @15
    crn
    #
    cun
    #
    cres
    #
    @15
    wss
    #
    wa
    #
    @18
    @15
    wss
    @19
    @16
    @14
    @0
    @13
    cvv
    wcel
    @14
    cvv
    wcel
    @11
    @12
    @0
    vx
    vex
    #
    dmex
    @0
    @27
    rnex
    unex
    @13
    cvv
    resiexg
    ax-mp
    @27
    unex
    a1i
    @20
    @25
    @0
    @14
    ssun2
    @24
    @14
    @15
    @23
    @13
    cid
    @23
    @13
    @13
    cun
    @13
    @21
    @13
    @22
    @13
    @21
    @14
    cdm
    #
    @11
    cun
    @13
    @11
    cun
    #
    @13
    @14
    @0
    dmun
    @28
    @13
    @11
    @13
    dmresi
    uneq1i
    @29
    @11
    @11
    cun
    #
    @12
    cun
    @13
    @11
    @12
    @11
    un23
    @30
    @11
    @12
    @11
    unidm
    uneq1i
    eqtri
    3eqtri
    @22
    @14
    crn
    #
    @12
    cun
    @13
    @12
    cun
    #
    @13
    @14
    @0
    rnun
    @31
    @13
    @12
    @13
    rnresi
    uneq1i
    @32
    @11
    @12
    @12
    cun
    #
    cun
    @13
    @11
    @12
    @12
    unass
    @33
    @12
    @11
    @12
    unidm
    uneq2i
    eqtri
    3eqtri
    uneq12i
    @13
    unidm
    eqtri
    reseq2i
    @14
    @0
    ssun1
    eqsstri
    pm3.2i
    @8
    @26
    vz
    @15
    cvv
    @7
    @25
    @1
    @15
    @0
    @1
    @15
    wceq
    #
    @6
    @24
    @1
    @15
    @34
    @5
    @23
    cid
    @34
    @3
    @21
    @4
    @22
    @1
    @15
    dmeq
    @1
    @15
    rneq
    uneq12d
    reseq2d
    @34
    id
    sseq12d
    cleq2lem
    intminss
    sylancl
    eqsstrd
    @16
    @8
    @15
    @1
    wss
    wi
    #
    vz
    wal
    #
    @15
    @10
    wss
    @36
    @16
    @35
    vz
    @8
    @14
    @0
    @1
    @8
    @14
    @6
    @1
    @2
    @14
    @6
    wss
    @7
    @2
    @14
    @6
    @13
    cres
    #
    @6
    @2
    @14
    cid
    @5
    @13
    cin
    #
    cres
    @37
    @2
    @13
    @38
    cid
    @2
    @13
    @13
    @5
    cin
    #
    @38
    @2
    @13
    @5
    wss
    #
    @13
    @39
    wceq
    @2
    @11
    @3
    wss
    @12
    @4
    wss
    @40
    @0
    @1
    dmss
    @0
    @1
    rnss
    @11
    @3
    @12
    @4
    unss12
    syl2anc
    @13
    @5
    dfss
    sylib
    @13
    @5
    incom
    syl6eq
    reseq2d
    cid
    @5
    @13
    resres
    syl6eqr
    @37
    @6
    wss
    @2
    @6
    @13
    resss
    a1i
    eqsstrd
    adantr
    @2
    @7
    simpr
    sstrd
    @2
    @7
    simpl
    unssd
    ax-gen
    a1i
    @8
    vz
    @15
    ssintab
    sylibr
    eqssd
    mpteq2ia
    eqtri
end
