include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cdm.mm"
include "cres.mm"
include "wa.mm"
include "crio.mm"
include "csuc.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "simpr3.mm"
include "wi.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfriota1.mm"
include "nfbr.mm"
include "nfn.mm"
include "nfral.mm"
include "nfim.mm"
include "wceq.mm"
include "simpl.mm"
include "wreu.mm"
include "wb.mm"
include "wrmo.mm"
include "rspe.mm"
include "adantr.mm"
include "nomaxmo.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "reu5.mm"
include "sylanbrc.mm"
include "riota1.mm"
include "syl.mm"
include "mpbid.mm"
include "simplr.mm"
include "nfra1.mm"
include "nfriota.mm"
include "nfeq.mm"
include "breq1.mm"
include "notbid.mm"
include "ralbid.mm"
include "biimprd.mm"
include "sylc.mm"
include "exp31.mm"
include "rexlimi.mm"
include "imp.mm"
include "breq2.mm"
include "rspc.mm"
include "wrel.mm"
include "wfun.mm"
include "simpr1.mm"
include "riotacl.mm"
include "sseldd.mm"
include "nofun.mm"
include "funrel.mm"
include "3syl.mm"
include "sssucid.mm"
include "relssres.mm"
include "sylancl.mm"
include "breq1d.mm"
include "con0.mm"
include "nodmon.mm"
include "sucelon.mm"
include "sylib.mm"
include "sltres.mm"
include "syl3anc.mm"
include "sylbird.mm"
include "mtod.mm"
include "noextendgt.mm"
include "noreson.mm"
include "syl2anc.mm"
include "c1o.mm"
include "2on.mm"
include "elexi.mm"
include "prid2.mm"
include "noextend.mm"
include "wor.mm"
include "sltso.mm"
include "sotr2.mm"
include "mpan.mm"
include "mp2and.mm"
include "cab.mm"
include "cfv.mm"
include "cio.mm"
include "cmpt.mm"
include "cif.mm"
include "iftrue.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "dmsnop.mm"
include "uneq2i.mm"
include "dmun.mm"
include "df-suc.mm"
include "3eqtr4i.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "3brtr4d.mm"
include "simpr2.mm"
include "nosupbnd1lem6.mm"
include "syl121anc.mm"
include "pm2.61ian.mm"

theorem nosupbnd1
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  assume nosupbnd1.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A g
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint U u
  disjoint u v
  disjoint U v
  disjoint u x
  disjoint U x
  disjoint u y
  disjoint U y
  disjoint v x
  disjoint v y
  disjoint x y
  assert |- ( ( A C_ No /\ A e. _V /\ U e. A ) -> ( U |` dom S ) <s S )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cslt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    cU
    cA
    wcel
    #
    w3a
    #
    cU
    cS
    cdm
    #
    cres
    #
    cS
    cslt
    wbr
    #
    @5
    @9
    wa
    #
    cU
    @4
    vx
    cA
    crio
    #
    cdm
    #
    csuc
    #
    cres
    #
    @14
    @15
    c2o
    cop
    csn
    #
    cun
    #
    @11
    cS
    cslt
    @13
    @14
    @17
    cslt
    wbr
    #
    wn
    #
    @14
    @19
    cslt
    wbr
    #
    @17
    @19
    cslt
    wbr
    #
    @13
    @20
    @14
    cU
    cslt
    wbr
    #
    @13
    @8
    @14
    @1
    cslt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @24
    wn
    #
    @5
    @6
    @7
    @8
    simpr3
    #
    @5
    @9
    @27
    @4
    @9
    @27
    wi
    vx
    cA
    @9
    @27
    vx
    @9
    vx
    nfv
    @26
    vx
    vy
    cA
    vx
    cA
    nfcv
    @25
    vx
    vx
    @14
    @1
    cslt
    @4
    vx
    cA
    nfriota1
    vx
    cslt
    nfcv
    vx
    @1
    nfcv
    nfbr
    nfn
    nfral
    nfim
    @0
    cA
    wcel
    #
    @4
    @9
    @27
    @30
    @4
    wa
    #
    @9
    wa
    #
    @14
    @0
    wceq
    #
    @4
    @27
    @32
    @31
    @33
    @31
    @9
    simpl
    @32
    @4
    vx
    cA
    wreu
    #
    @31
    @33
    wb
    @32
    @5
    @4
    vx
    cA
    wrmo
    #
    @34
    @31
    @5
    @9
    @4
    vx
    cA
    rspe
    adantr
    @9
    @35
    @31
    @6
    @7
    @35
    @8
    vx
    vy
    cA
    nomaxmo
    3ad2ant1
    #
    adantl
    @4
    vx
    cA
    reu5
    #
    sylanbrc
    @4
    vx
    cA
    riota1
    syl
    mpbid
    @30
    @4
    @9
    simplr
    @33
    @27
    @4
    @33
    @26
    @3
    vy
    cA
    vy
    @14
    @0
    @4
    vy
    vx
    cA
    @3
    vy
    cA
    nfra1
    vy
    cA
    nfcv
    nfriota
    #
    vy
    @0
    nfcv
    nfeq
    @33
    @25
    @2
    @14
    @0
    @1
    cslt
    breq1
    notbid
    ralbid
    biimprd
    sylc
    exp31
    rexlimi
    imp
    @26
    @28
    vy
    cU
    cA
    @24
    vy
    vy
    @14
    cU
    cslt
    @38
    vy
    cslt
    nfcv
    vy
    cU
    nfcv
    nfbr
    nfn
    @1
    cU
    wceq
    @25
    @24
    @1
    cU
    @14
    cslt
    breq2
    notbid
    rspc
    sylc
    @13
    @20
    @14
    @16
    cres
    #
    @17
    cslt
    wbr
    #
    @24
    @13
    @39
    @14
    @17
    cslt
    @13
    @14
    wrel
    #
    @15
    @16
    wss
    @39
    @14
    wceq
    @13
    @14
    csur
    wcel
    #
    @14
    wfun
    @41
    @13
    cA
    csur
    @14
    @5
    @6
    @7
    @8
    simpr1
    #
    @13
    @34
    @14
    cA
    wcel
    @13
    @5
    @35
    @34
    @5
    @9
    simpl
    @9
    @35
    @5
    @36
    adantl
    @37
    sylanbrc
    @4
    vx
    cA
    riotacl
    syl
    sseldd
    #
    @14
    nofun
    @14
    funrel
    3syl
    @15
    sssucid
    @14
    @16
    relssres
    sylancl
    breq1d
    @13
    @42
    cU
    csur
    wcel
    #
    @16
    con0
    wcel
    #
    @40
    @24
    wi
    @44
    @13
    cA
    csur
    cU
    @43
    @29
    sseldd
    #
    @13
    @15
    con0
    wcel
    #
    @46
    @13
    @42
    @48
    @44
    @14
    nodmon
    syl
    @15
    sucelon
    sylib
    #
    @14
    cU
    @16
    sltres
    syl3anc
    sylbird
    mtod
    @13
    @42
    @22
    @44
    @14
    noextendgt
    syl
    @13
    @17
    csur
    wcel
    #
    @42
    @19
    csur
    wcel
    #
    @21
    @22
    wa
    @23
    wi
    #
    @13
    @45
    @46
    @50
    @47
    @49
    cU
    @16
    noreson
    syl2anc
    @44
    @13
    @42
    @51
    @44
    @14
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    #
    prid2
    noextend
    syl
    csur
    cslt
    wor
    @50
    @42
    @51
    w3a
    @52
    sltso
    csur
    @17
    @14
    @19
    cslt
    sotr2
    mpan
    syl3anc
    mp2and
    @13
    @10
    @16
    cU
    @5
    @10
    @16
    wceq
    @9
    @5
    @10
    @19
    cdm
    #
    @16
    @5
    cS
    @19
    @5
    cS
    @5
    @19
    vg
    @1
    vu
    cv
    #
    cdm
    #
    wcel
    vv
    cv
    #
    @55
    cslt
    wbr
    wn
    #
    @55
    @1
    csuc
    #
    cres
    @57
    @59
    cres
    wceq
    wi
    vv
    cA
    wral
    wa
    vu
    cA
    wrex
    vy
    cab
    vg
    cv
    #
    @56
    wcel
    @58
    @55
    @60
    csuc
    #
    cres
    @57
    @61
    cres
    wceq
    wi
    vv
    cA
    wral
    @60
    @55
    cfv
    @0
    wceq
    w3a
    vu
    cA
    wrex
    vx
    cio
    cmpt
    #
    cif
    @19
    nosupbnd1.1
    @5
    @19
    @62
    iftrue
    syl5eq
    #
    dmeqd
    @15
    @18
    cdm
    #
    cun
    @15
    @15
    csn
    #
    cun
    @54
    @16
    @64
    @65
    @15
    @15
    c2o
    @53
    dmsnop
    uneq2i
    @14
    @18
    dmun
    @15
    df-suc
    3eqtr4i
    syl6eq
    adantr
    reseq2d
    @5
    cS
    @19
    wceq
    @9
    @63
    adantr
    3brtr4d
    @5
    wn
    #
    @9
    wa
    @66
    @6
    @7
    @8
    @12
    @66
    @9
    simpl
    @66
    @6
    @7
    @8
    simpr1
    @66
    @6
    @7
    @8
    simpr2
    @66
    @6
    @7
    @8
    simpr3
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    nosupbnd1.1
    nosupbnd1lem6
    syl121anc
    pm2.61ian
end
