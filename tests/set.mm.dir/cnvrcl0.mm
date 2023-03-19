include "wcel.mm"
include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wss.mm"
include "ccnv.mm"
include "cdif.mm"
include "wceq.mm"
include "wi.mm"
include "cnvresid.mm"
include "c0.mm"
include "cnvnonrel.mm"
include "cnv0.mm"
include "eqtr4i.mm"
include "dmeqi.mm"
include "df-rn.mm"
include "3eqtr4i.mm"
include "0ss.mm"
include "rnss.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "rnun.mm"
include "dfdm4.mm"
include "3eqtr4ri.mm"
include "rneqi.mm"
include "dmss.mm"
include "dmun.mm"
include "uneq12i.mm"
include "equncomi.mm"
include "reseq2i.mm"
include "eqtr2i.mm"
include "cnvss.mm"
include "syl5eqss.mm"
include "ssun1.mm"
include "syl6ss.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "a1i.mm"
include "cvv.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "resiexd.mm"
include "mpdan.mm"
include "wa.mm"
include "dmresi.mm"
include "eqimssi.mm"
include "unssi.mm"
include "ssun2.mm"
include "rnresi.mm"
include "pm3.2i.mm"
include "unss.mm"
include "ssres2.mm"
include "sylbi.mm"
include "ssun4.mm"
include "mp2b.mm"
include "clcnvlem.mm"

theorem cnvrcl0
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let cX: class X

  disjoint x y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  assert |- ( X e. V -> `' |^| { x | ( X C_ x /\ ( _I |` ( dom x u. ran x ) ) C_ x ) } = |^| { y | ( `' X C_ y /\ ( _I |` ( dom y u. ran y ) ) C_ y ) } )

  proof
    cX
    cV
    wcel
    #
    cid
    vx
    cv
    #
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
    cid
    vy
    cv
    #
    cdm
    #
    @7
    crn
    #
    cun
    #
    cres
    #
    @7
    wss
    #
    cid
    cX
    cid
    cX
    cdm
    #
    cX
    crn
    #
    cun
    #
    cres
    #
    cun
    #
    cdm
    #
    @17
    crn
    #
    cun
    #
    cres
    #
    @17
    wss
    #
    vx
    vy
    @17
    cX
    @1
    @7
    ccnv
    #
    cX
    cX
    ccnv
    ccnv
    cdif
    #
    cun
    #
    wceq
    #
    @12
    @6
    wi
    @0
    @12
    @6
    @26
    cid
    @25
    cdm
    #
    @25
    crn
    #
    cun
    #
    cres
    #
    @25
    wss
    @12
    @30
    @23
    @25
    @12
    @30
    @11
    ccnv
    #
    @23
    @31
    @11
    @30
    @10
    cnvresid
    @10
    @29
    cid
    @10
    @28
    @27
    @8
    @28
    @9
    @27
    @23
    crn
    #
    @24
    crn
    #
    cun
    #
    @32
    @28
    @8
    @33
    @32
    wss
    @34
    @32
    wceq
    @33
    c0
    crn
    #
    @32
    @24
    ccnv
    #
    cdm
    c0
    ccnv
    #
    cdm
    @33
    @35
    @36
    @37
    @36
    c0
    @37
    cX
    cnvnonrel
    cnv0
    eqtr4i
    #
    dmeqi
    @24
    df-rn
    c0
    df-rn
    3eqtr4i
    c0
    @23
    wss
    #
    @35
    @32
    wss
    @23
    0ss
    #
    c0
    @23
    rnss
    ax-mp
    eqsstri
    @33
    @32
    ssequn2
    mpbi
    @23
    @24
    rnun
    @7
    dfdm4
    3eqtr4ri
    @23
    cdm
    #
    @24
    cdm
    #
    cun
    #
    @41
    @27
    @9
    @42
    @41
    wss
    @43
    @41
    wceq
    @42
    c0
    cdm
    #
    @41
    @36
    crn
    @37
    crn
    @42
    @44
    @36
    @37
    @38
    rneqi
    @24
    dfdm4
    c0
    dfdm4
    3eqtr4i
    @39
    @44
    @41
    wss
    @40
    c0
    @23
    dmss
    ax-mp
    eqsstri
    @42
    @41
    ssequn2
    mpbi
    @23
    @24
    dmun
    @7
    df-rn
    3eqtr4ri
    uneq12i
    equncomi
    reseq2i
    eqtr2i
    @11
    @7
    cnvss
    syl5eqss
    @23
    @24
    ssun1
    syl6ss
    @26
    @5
    @30
    @1
    @25
    @26
    @4
    @29
    cid
    @26
    @2
    @27
    @3
    @28
    @1
    @25
    dmeq
    @1
    @25
    rneq
    uneq12d
    reseq2d
    @26
    id
    sseq12d
    syl5ibr
    adantl
    @7
    @1
    ccnv
    #
    wceq
    #
    @6
    @12
    wi
    @0
    @6
    @12
    @46
    cid
    @45
    cdm
    #
    @45
    crn
    #
    cun
    #
    cres
    #
    @45
    wss
    @6
    @50
    @5
    ccnv
    #
    @45
    @51
    @5
    @50
    @4
    cnvresid
    @4
    @49
    cid
    @4
    @48
    @47
    @2
    @48
    @3
    @47
    @1
    dfdm4
    @1
    df-rn
    uneq12i
    equncomi
    reseq2i
    eqtr2i
    @5
    @1
    cnvss
    syl5eqss
    @46
    @11
    @50
    @7
    @45
    @46
    @10
    @49
    cid
    @46
    @8
    @47
    @9
    @48
    @7
    @45
    dmeq
    @7
    @45
    rneq
    uneq12d
    reseq2d
    @46
    id
    sseq12d
    syl5ibr
    adantl
    @1
    @17
    wceq
    #
    @5
    @21
    @1
    @17
    @52
    @4
    @20
    cid
    @52
    @2
    @18
    @3
    @19
    @1
    @17
    dmeq
    @1
    @17
    rneq
    uneq12d
    reseq2d
    @52
    id
    sseq12d
    cX
    @17
    wss
    @0
    cX
    @16
    ssun1
    a1i
    @0
    @16
    cvv
    wcel
    @17
    cvv
    wcel
    @0
    @15
    cvv
    @0
    @13
    cvv
    wcel
    @14
    cvv
    wcel
    @15
    cvv
    wcel
    cX
    cV
    dmexg
    cX
    cV
    rnexg
    @13
    @14
    cvv
    cvv
    unexg
    syl2anc
    resiexd
    cX
    @16
    cV
    cvv
    unexg
    mpdan
    @22
    @0
    @18
    @15
    wss
    #
    @19
    @15
    wss
    #
    wa
    #
    @21
    @16
    wss
    #
    @22
    @53
    @54
    @18
    @13
    @16
    cdm
    #
    cun
    @15
    cX
    @16
    dmun
    @13
    @57
    @15
    @13
    @14
    ssun1
    @57
    @15
    @15
    dmresi
    eqimssi
    unssi
    eqsstri
    @19
    @14
    @16
    crn
    #
    cun
    @15
    cX
    @16
    rnun
    @14
    @58
    @15
    @14
    @13
    ssun2
    @58
    @15
    @15
    rnresi
    eqimssi
    unssi
    eqsstri
    pm3.2i
    @55
    @20
    @15
    wss
    @56
    @18
    @19
    @15
    unss
    @20
    @15
    cid
    ssres2
    sylbi
    @21
    @16
    cX
    ssun4
    mp2b
    a1i
    clcnvlem
end
