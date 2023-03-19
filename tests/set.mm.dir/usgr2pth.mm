include "cusgr.mm"
include "wcel.mm"
include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1.mm"
include "cfz.mm"
include "cv.mm"
include "c1.mm"
include "w3a.mm"
include "cpr.mm"
include "cdif.mm"
include "wrex.mm"
include "csn.mm"
include "wi.mm"
include "cspths.mm"
include "usgr2pthspth.mm"
include "cupgr.mm"
include "usgrupgr.mm"
include "adantr.mm"
include "ctrls.mm"
include "ccnv.mm"
include "wfun.mm"
include "wb.mm"
include "isspth.mm"
include "a1i.mm"
include "wf.mm"
include "caddc.mm"
include "wral.mm"
include "upgrf1istrl.mm"
include "anbi1d.mm"
include "oveq2.mm"
include "f1eq2.mm"
include "syl.mm"
include "biimpd.mm"
include "adantl.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "ad2antrl.mm"
include "feq2d.mm"
include "df-f1.mm"
include "simplbi2.mm"
include "sylbid.mm"
include "com3l.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "usgr2pthlem.mm"
include "3jcad.mm"
include "ex.mm"
include "com23.mm"
include "mpcom.mm"
include "com13.mm"
include "cn0.mm"
include "2nn0.mm"
include "f1f.mm"
include "fnfzo0hash.mm"
include "sylancr.mm"
include "eqcoms.mm"
include "ad2antrr.mm"
include "syl5ib.mm"
include "eqcom.mm"
include "biimpi.mm"
include "preq12d.mm"
include "eqeq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "3ad2ant3.mm"
include "jca.mm"
include "rexlimivw.mm"
include "a1i13.mm"
include "fzo0to2pr.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "2wlklem.mm"
include "syl6bb.mm"
include "imbi2d.mm"
include "sylibrd.mm"
include "3jca.mm"
include "simprbi.mm"
include "bitrd.mm"
include "mpbird.mm"
include "simpr.mm"
include "simp-4l.mm"
include "syl2anc.mm"
include "exp41.mm"
include "3imp.mm"
include "impbid.mm"

theorem usgr2pth
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vi: setvar i
  assume usgr2pthlem.v: |- V = ( Vtx ` G )
  assume usgr2pthlem.i: |- I = ( iEdg ` G )

  disjoint F x
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint F i
  disjoint I i
  disjoint P i
  disjoint G i
  disjoint V i
  assert |- ( G e. USGraph -> ( ( F ( Paths ` G ) P /\ ( # ` F ) = 2 ) <-> ( F : ( 0 ..^ 2 ) -1-1-> dom I /\ P : ( 0 ... 2 ) -1-1-> V /\ E. x e. V E. y e. ( V \ { x } ) E. z e. ( V \ { x , y } ) ( ( ( P ` 0 ) = x /\ ( P ` 1 ) = y /\ ( P ` 2 ) = z ) /\ ( ( I ` ( F ` 0 ) ) = { x , y } /\ ( I ` ( F ` 1 ) ) = { y , z } ) ) ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    cc0
    c2
    cfzo
    co
    #
    cI
    cdm
    #
    cF
    wf1
    #
    cc0
    c2
    cfz
    co
    #
    cV
    cP
    wf1
    #
    cc0
    cP
    cfv
    #
    vx
    cv
    #
    wceq
    #
    c1
    cP
    cfv
    #
    vy
    cv
    #
    wceq
    #
    c2
    cP
    cfv
    #
    vz
    cv
    #
    wceq
    #
    w3a
    #
    cc0
    cF
    cfv
    cI
    cfv
    #
    @11
    @14
    cpr
    #
    wceq
    #
    c1
    cF
    cfv
    cI
    cfv
    #
    @14
    @17
    cpr
    #
    wceq
    #
    wa
    #
    wa
    #
    vz
    cV
    @21
    cdif
    #
    wrex
    #
    vy
    cV
    @11
    csn
    cdif
    #
    wrex
    #
    vx
    cV
    wrex
    #
    w3a
    #
    @4
    @0
    @33
    @1
    @3
    @0
    @33
    wi
    @0
    @3
    @1
    @33
    @0
    @3
    @1
    @33
    wi
    @0
    @3
    wa
    #
    @1
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    @33
    cP
    cF
    cG
    usgr2pthspth
    #
    cG
    cupgr
    wcel
    #
    @34
    @35
    @33
    wi
    @0
    @37
    @3
    cG
    usgrupgr
    #
    adantr
    @37
    @35
    @34
    @33
    @37
    @35
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    ccnv
    wfun
    #
    wa
    #
    @34
    @33
    wi
    #
    @35
    @41
    wb
    @37
    cP
    cF
    cG
    isspth
    a1i
    #
    @37
    @41
    cc0
    @2
    cfzo
    co
    #
    @6
    cF
    wf1
    #
    cc0
    @2
    cfz
    co
    #
    cV
    cP
    wf
    #
    vi
    cv
    #
    cF
    cfv
    cI
    cfv
    @48
    cP
    cfv
    @48
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    #
    vi
    @44
    wral
    #
    w3a
    #
    @40
    wa
    #
    @42
    @37
    @39
    @51
    @40
    cP
    vi
    cF
    cG
    cI
    cV
    usgr2pthlem.v
    usgr2pthlem.i
    upgrf1istrl
    anbi1d
    #
    @37
    @52
    @42
    @37
    @52
    wa
    @34
    @7
    @9
    @32
    @51
    @34
    @7
    wi
    #
    @37
    @40
    @45
    @47
    @54
    @50
    @34
    @45
    @7
    @3
    @45
    @7
    wi
    @0
    @3
    @45
    @7
    @3
    @44
    @5
    wceq
    @45
    @7
    wb
    @2
    c2
    cc0
    cfzo
    oveq2
    #
    @44
    @5
    @6
    cF
    f1eq2
    syl
    biimpd
    adantl
    com12
    3ad2ant1
    ad2antrl
    @52
    @34
    @9
    wi
    #
    @37
    @51
    @40
    @56
    @47
    @45
    @40
    @56
    wi
    @50
    @34
    @47
    @40
    @9
    @3
    @47
    @40
    @9
    wi
    #
    wi
    @0
    @3
    @47
    @8
    cV
    cP
    wf
    #
    @57
    @3
    @46
    @8
    cV
    cP
    @2
    c2
    cc0
    cfz
    oveq2
    feq2d
    @58
    @57
    wi
    @3
    @9
    @58
    @40
    @8
    cV
    cP
    df-f1
    #
    simplbi2
    a1i
    sylbid
    adantl
    com3l
    3ad2ant2
    imp
    adantl
    @51
    @34
    @32
    wi
    @37
    @40
    vx
    vy
    vz
    cP
    vi
    cF
    cG
    cI
    cV
    usgr2pthlem.v
    usgr2pthlem.i
    usgr2pthlem
    ad2antrl
    3jcad
    ex
    sylbid
    sylbid
    com23
    mpcom
    sylbid
    ex
    com13
    imp
    com12
    @33
    @0
    @4
    @7
    @9
    @32
    @0
    @4
    wi
    #
    @3
    @7
    @9
    @32
    @60
    wi
    wi
    @7
    c2
    cn0
    wcel
    @5
    @6
    cF
    wf
    @3
    2nn0
    @5
    @6
    cF
    f1f
    @6
    cF
    c2
    fnfzo0hash
    sylancr
    @3
    @7
    @9
    @32
    @60
    @3
    @7
    wa
    #
    @9
    wa
    #
    @32
    wa
    #
    @0
    @4
    @63
    @0
    wa
    #
    @1
    @3
    @64
    @1
    @35
    @64
    @35
    @52
    @64
    @51
    @40
    @64
    @45
    @47
    @50
    @62
    @45
    @32
    @0
    @61
    @45
    @9
    @3
    @7
    @45
    @3
    @7
    @45
    @3
    @5
    @44
    wceq
    #
    @7
    @45
    wb
    @65
    c2
    @2
    c2
    @2
    cc0
    cfzo
    oveq2
    eqcoms
    @5
    @44
    @6
    cF
    f1eq2
    syl
    biimpd
    imp
    adantr
    ad2antrr
    @62
    @47
    @32
    @0
    @61
    @9
    @47
    @9
    @58
    @61
    @47
    @8
    cV
    cP
    f1f
    @61
    @8
    @46
    cV
    cP
    @3
    @8
    @46
    wceq
    #
    @7
    @66
    c2
    @2
    c2
    @2
    cc0
    cfz
    oveq2
    eqcoms
    adantr
    feq2d
    syl5ib
    imp
    ad2antrr
    @63
    @0
    @50
    @62
    @32
    @0
    @50
    wi
    #
    @3
    @32
    @67
    wi
    @7
    @9
    @3
    @32
    @0
    @20
    @10
    @13
    cpr
    #
    wceq
    #
    @23
    @13
    @16
    cpr
    #
    wceq
    #
    wa
    #
    wi
    @67
    @3
    @32
    @0
    @72
    @31
    @72
    vx
    cV
    @29
    @72
    vy
    @30
    @27
    @72
    vz
    @28
    @27
    @69
    @71
    @26
    @19
    @69
    @22
    @19
    @69
    wi
    @25
    @19
    @22
    @69
    @19
    @21
    @68
    @20
    @19
    @11
    @10
    @14
    @13
    @12
    @15
    @11
    @10
    wceq
    #
    @18
    @12
    @73
    @10
    @11
    eqcom
    biimpi
    3ad2ant1
    @15
    @12
    @14
    @13
    wceq
    #
    @18
    @15
    @74
    @13
    @14
    eqcom
    biimpi
    3ad2ant2
    #
    preq12d
    eqeq2d
    biimpcd
    adantr
    impcom
    @26
    @19
    @71
    @25
    @19
    @71
    wi
    @22
    @19
    @25
    @71
    @19
    @24
    @70
    @23
    @19
    @14
    @13
    @17
    @16
    @75
    @18
    @12
    @17
    @16
    wceq
    #
    @15
    @18
    @76
    @16
    @17
    eqcom
    biimpi
    3ad2ant3
    preq12d
    eqeq2d
    biimpcd
    adantl
    impcom
    jca
    rexlimivw
    rexlimivw
    rexlimivw
    a1i13
    @3
    @50
    @72
    @0
    @3
    @50
    @49
    vi
    cc0
    c1
    cpr
    #
    wral
    @72
    @3
    @49
    vi
    @44
    @77
    @3
    @44
    @5
    @77
    @55
    fzo0to2pr
    syl6eq
    raleqdv
    cP
    vi
    cI
    cF
    2wlklem
    syl6bb
    imbi2d
    sylibrd
    ad2antrr
    imp
    imp
    3jca
    @62
    @40
    @32
    @0
    @9
    @40
    @61
    @9
    @58
    @40
    @59
    simprbi
    adantl
    ad2antrr
    jca
    @0
    @35
    @52
    wb
    #
    @63
    @0
    @37
    @78
    @38
    @37
    @35
    @41
    @52
    @43
    @53
    bitrd
    syl
    adantl
    mpbird
    @64
    @0
    @3
    @1
    @35
    wb
    @63
    @0
    simpr
    @3
    @7
    @9
    @32
    @0
    simp-4l
    #
    @36
    syl2anc
    mpbird
    @79
    jca
    ex
    exp41
    mpcom
    3imp
    com12
    impbid
end
