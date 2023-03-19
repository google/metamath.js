include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "cfv.mm"
include "cima.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cdif.mm"
include "cuni.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "snidb.mm"
include "fvres.mm"
include "sylbi.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "funfv.mm"
include "wss.mm"
include "wrel.mm"
include "df-fun.mm"
include "simprbi.mm"
include "ssdif0.mm"
include "sylib.mm"
include "unieqd.mm"
include "uni0.mm"
include "syl6eq.mm"
include "difeq2d.mm"
include "resima.mm"
include "dif0.mm"
include "eqtr4i.mm"
include "syl6reqr.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "nfunsn.mm"
include "cdm.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "relres.mm"
include "dffun3.mm"
include "mpbiran.mm"
include "iman.mm"
include "albii.mm"
include "alnex.mm"
include "bitri.mm"
include "exbii.mm"
include "exnal.mm"
include "3bitrri.mm"
include "con1bii.mm"
include "sp.mm"
include "eximi.mm"
include "snssi.mm"
include "residm.mm"
include "dmeqi.mm"
include "ssdmres.mm"
include "biimpi.mm"
include "syl.mm"
include "vex.mm"
include "breldm.mm"
include "eleq2.mm"
include "velsn.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "syl2an.mm"
include "breq1d.mm"
include "biimpd.mm"
include "ex.mm"
include "pm2.43d.mm"
include "anim1d.mm"
include "eximdv.mm"
include "exlimdv.mm"
include "mpan9.mm"
include "eleq2i.mm"
include "elimasni.mm"
include "sylbir.mm"
include "cpr.mm"
include "cop.mm"
include "uniop.mm"
include "opex.mm"
include "unisn.mm"
include "wrex.mm"
include "wb.mm"
include "brrelexi.mm"
include "brcnvg.mm"
include "sylancr.mm"
include "biimpar.mm"
include "adantl.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpancom.mm"
include "ancoms.mm"
include "syldan.mm"
include "anim1i.mm"
include "an32s.mm"
include "eldif.mm"
include "rexv.mm"
include "brco.mm"
include "df-br.mm"
include "3bitr2ri.mm"
include "ideq.mm"
include "equcom.mm"
include "3bitr3i.mm"
include "notbii.mm"
include "anbi12i.mm"
include "bitr2i.mm"
include "uniss.mm"
include "3syl.mm"
include "syl5eqssr.mm"
include "unissd.mm"
include "prss.mm"
include "sylibr.mm"
include "simpld.mm"
include "syl5.mm"
include "exlimiv.mm"
include "ssrdv.mm"
include "ndmima.mm"
include "difeq1d.mm"
include "0dif.mm"
include "pm2.61d1.mm"

theorem dffv2
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( F ` A ) = U. ( ( F " { A } ) \ U. U. ( ( ( F |` { A } ) o. `' ( F |` { A } ) ) \ _I ) )

  proof
    cF
    cA
    csn
    #
    cres
    #
    wfun
    #
    cA
    cF
    cfv
    #
    cF
    @0
    cima
    #
    @1
    @1
    ccnv
    #
    ccom
    #
    cid
    cdif
    #
    cuni
    #
    cuni
    #
    cdif
    #
    cuni
    #
    wceq
    @2
    @3
    cA
    @1
    cfv
    #
    @11
    cA
    cvv
    wcel
    #
    @12
    @3
    wceq
    #
    @13
    cA
    @0
    wcel
    @14
    cA
    snidb
    cA
    @0
    cF
    fvres
    sylbi
    @13
    wn
    @12
    c0
    @3
    cA
    @1
    fvprc
    cA
    cF
    fvprc
    eqtr4d
    pm2.61i
    @2
    @12
    @1
    @0
    cima
    #
    cuni
    @11
    cA
    @1
    funfv
    @2
    @15
    @10
    @2
    @10
    @4
    c0
    cdif
    #
    @15
    @2
    @9
    c0
    @4
    @2
    @9
    c0
    cuni
    #
    c0
    @2
    @8
    c0
    @2
    @8
    @17
    c0
    @2
    @7
    c0
    @2
    @6
    cid
    wss
    #
    @7
    c0
    wceq
    @2
    @1
    wrel
    #
    @18
    @1
    df-fun
    simprbi
    @6
    cid
    ssdif0
    sylib
    unieqd
    uni0
    syl6eq
    unieqd
    uni0
    syl6eq
    difeq2d
    @15
    @4
    @16
    cF
    @0
    resima
    #
    @4
    dif0
    eqtr4i
    syl6reqr
    unieqd
    eqtrd
    syl5eqr
    @2
    wn
    #
    @3
    c0
    @11
    cA
    cF
    nfunsn
    @21
    @11
    @17
    c0
    @21
    @10
    c0
    @21
    cA
    @1
    cdm
    #
    wcel
    #
    @10
    c0
    wceq
    #
    @21
    @23
    @24
    @21
    @23
    wa
    #
    @4
    @9
    wss
    @24
    @25
    vy
    @4
    @9
    @25
    cA
    vz
    cv
    #
    @1
    wbr
    #
    vz
    vy
    weq
    #
    wn
    #
    wa
    #
    vz
    wex
    #
    vy
    cv
    #
    @4
    wcel
    #
    @32
    @9
    wcel
    #
    wi
    #
    @21
    vx
    cv
    #
    @26
    @1
    wbr
    #
    @29
    wa
    #
    vz
    wex
    #
    vx
    wex
    #
    @23
    @31
    @21
    @39
    vy
    wal
    #
    vx
    wex
    #
    @40
    @42
    @2
    @2
    @37
    @28
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vx
    wal
    #
    @41
    wn
    #
    vx
    wal
    @42
    wn
    @2
    @19
    @46
    cF
    @0
    relres
    #
    vx
    vz
    vy
    @1
    dffun3
    mpbiran
    @45
    @47
    vx
    @45
    @39
    wn
    #
    vy
    wex
    @47
    @44
    @49
    vy
    @44
    @38
    wn
    #
    vz
    wal
    @49
    @43
    @50
    vz
    @37
    @28
    iman
    albii
    @38
    vz
    alnex
    bitri
    exbii
    @39
    vy
    exnal
    bitri
    albii
    @41
    vx
    alnex
    3bitrri
    con1bii
    @41
    @39
    vx
    @39
    vy
    sp
    eximi
    sylbi
    @23
    @39
    @31
    vx
    @23
    @38
    @30
    vz
    @23
    @37
    @27
    @29
    @23
    @37
    @27
    @23
    @37
    @37
    @27
    wi
    @23
    @37
    wa
    #
    @37
    @27
    @51
    @36
    cA
    @26
    @1
    @23
    @22
    @0
    wceq
    #
    @36
    @22
    wcel
    #
    @36
    cA
    wceq
    #
    @37
    @23
    @0
    @22
    wss
    #
    @52
    cA
    @22
    snssi
    @55
    @22
    @1
    @0
    cres
    #
    cdm
    #
    @0
    @56
    @1
    cF
    @0
    residm
    dmeqi
    @55
    @57
    @0
    wceq
    @0
    @1
    ssdmres
    biimpi
    syl5eqr
    syl
    @36
    @26
    @1
    vx
    vex
    vz
    vex
    #
    breldm
    @52
    @53
    @54
    @52
    @53
    @36
    @0
    wcel
    @54
    @22
    @0
    @36
    eleq2
    vx
    cA
    velsn
    syl6bb
    biimpa
    syl2an
    breq1d
    biimpd
    ex
    pm2.43d
    anim1d
    eximdv
    exlimdv
    mpan9
    @30
    @35
    vz
    @33
    cA
    @32
    @1
    wbr
    #
    @30
    @34
    @33
    @32
    @15
    wcel
    @59
    @15
    @4
    @32
    @20
    eleq2i
    @1
    cA
    @32
    elimasni
    sylbir
    @30
    @59
    @34
    @30
    @59
    wa
    #
    @34
    @26
    @9
    wcel
    #
    @60
    @32
    @26
    cpr
    #
    @9
    wss
    @34
    @61
    wa
    @60
    @62
    @32
    @26
    cop
    #
    cuni
    @9
    @32
    @26
    vy
    vex
    #
    @58
    uniop
    @60
    @63
    @8
    @60
    @63
    @63
    csn
    #
    cuni
    #
    @8
    @63
    @32
    @26
    opex
    unisn
    @60
    @63
    @7
    wcel
    #
    @65
    @7
    wss
    @66
    @8
    wss
    @60
    @32
    @36
    @5
    wbr
    #
    @37
    wa
    #
    vx
    cvv
    wrex
    #
    @29
    wa
    #
    @67
    @27
    @59
    @29
    @71
    @27
    @59
    wa
    @70
    @29
    @27
    @59
    @32
    cA
    @5
    wbr
    #
    @70
    @27
    @72
    @59
    @27
    @32
    cvv
    wcel
    @13
    @72
    @59
    wb
    @64
    cA
    @26
    @1
    @48
    brrelexi
    #
    @32
    cA
    cvv
    cvv
    @1
    brcnvg
    sylancr
    biimpar
    @72
    @27
    @70
    @13
    @72
    @27
    wa
    #
    @70
    @27
    @13
    @72
    @73
    adantl
    @69
    @74
    vx
    cA
    cvv
    @54
    @68
    @72
    @37
    @27
    @36
    cA
    @32
    @5
    breq2
    @36
    cA
    @26
    @1
    breq1
    anbi12d
    rspcev
    mpancom
    ancoms
    syldan
    anim1i
    an32s
    @67
    @63
    @6
    wcel
    #
    @63
    cid
    wcel
    #
    wn
    #
    wa
    @71
    @63
    @6
    cid
    eldif
    @75
    @70
    @77
    @29
    @70
    @69
    vx
    wex
    @32
    @26
    @6
    wbr
    @75
    @69
    vx
    rexv
    vx
    @32
    @26
    @1
    @5
    @64
    @58
    brco
    @32
    @26
    @6
    df-br
    3bitr2ri
    @76
    @28
    @32
    @26
    cid
    wbr
    vy
    vz
    weq
    @76
    @28
    @32
    @26
    @58
    ideq
    @32
    @26
    cid
    df-br
    vy
    vz
    equcom
    3bitr3i
    notbii
    anbi12i
    bitr2i
    sylib
    @63
    @7
    snssi
    @65
    @7
    uniss
    3syl
    syl5eqssr
    unissd
    syl5eqssr
    @32
    @26
    @9
    @64
    @58
    prss
    sylibr
    simpld
    ex
    syl5
    exlimiv
    syl
    ssrdv
    @4
    @9
    ssdif0
    sylib
    ex
    @23
    wn
    #
    @10
    c0
    @9
    cdif
    c0
    @78
    @4
    c0
    @9
    @78
    @4
    @15
    c0
    @20
    cA
    @1
    ndmima
    syl5eqr
    difeq1d
    @9
    0dif
    syl6eq
    pm2.61d1
    unieqd
    uni0
    syl6eq
    eqtr4d
    pm2.61i
end
