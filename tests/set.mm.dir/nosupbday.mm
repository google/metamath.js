include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cbday.mm"
include "cfv.mm"
include "cdm.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "wceq.mm"
include "nosupno.mm"
include "bdayval.mm"
include "syl.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "crio.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cres.mm"
include "wi.mm"
include "cab.mm"
include "w3a.mm"
include "cio.mm"
include "cmpt.mm"
include "cif.mm"
include "iftrue.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "con0.mm"
include "2on.mm"
include "elexi.mm"
include "dmsnop.mm"
include "uneq2i.mm"
include "dmun.mm"
include "df-suc.mm"
include "3eqtr4i.mm"
include "syl6eq.mm"
include "adantr.mm"
include "simprl.mm"
include "wreu.mm"
include "wrmo.mm"
include "simpl.mm"
include "nomaxmo.mm"
include "adantl.mm"
include "reu5.mm"
include "sylanbrc.mm"
include "riotacl.mm"
include "sseldd.mm"
include "wfn.mm"
include "wfo.mm"
include "bdayfo.mm"
include "fofn.mm"
include "ax-mp.mm"
include "fnfvima.mm"
include "mp3an2i.mm"
include "eqeltrrd.mm"
include "elssuni.mm"
include "word.mm"
include "wb.mm"
include "nodmord.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "sseqtri.mm"
include "ssorduni.mm"
include "ordsucsssuc.mm"
include "sylancl.mm"
include "mpbid.mm"
include "eqsstrd.mm"
include "iffalse.mm"
include "iotaex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "ssel2.mm"
include "mp3an1.mm"
include "adantlr.mm"
include "sssucid.mm"
include "syl6ss.mm"
include "sseld.mm"
include "adantrd.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "pm2.61ian.mm"

theorem nosupbday
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let vg: setvar g
  assume nosupbday.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A g
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  assert |- ( ( A C_ No /\ A e. _V ) -> ( bday ` S ) C_ suc U. ( bday " A ) )

  proof
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cS
    cbday
    cfv
    #
    cS
    cdm
    #
    cbday
    cA
    cima
    #
    cuni
    #
    csuc
    #
    @2
    cS
    csur
    wcel
    @3
    @4
    wceq
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    cvv
    nosupbday.1
    nosupno
    cS
    bdayval
    syl
    vx
    cv
    #
    vy
    cv
    #
    cslt
    wbr
    wn
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @2
    @4
    @7
    wss
    @11
    @2
    wa
    #
    @4
    @10
    vx
    cA
    crio
    #
    cdm
    #
    csuc
    #
    @7
    @11
    @4
    @15
    wceq
    @2
    @11
    @4
    @13
    @14
    c2o
    cop
    csn
    #
    cun
    #
    cdm
    #
    @15
    @11
    cS
    @17
    @11
    cS
    @11
    @17
    vg
    @9
    vu
    cv
    #
    cdm
    #
    wcel
    #
    vv
    cv
    #
    @19
    cslt
    wbr
    wn
    #
    @19
    @9
    csuc
    #
    cres
    @22
    @24
    cres
    wceq
    wi
    vv
    cA
    wral
    #
    wa
    #
    vu
    cA
    wrex
    #
    vy
    cab
    #
    vg
    cv
    #
    @20
    wcel
    @23
    @19
    @29
    csuc
    #
    cres
    @22
    @30
    cres
    wceq
    wi
    vv
    cA
    wral
    @29
    @19
    cfv
    @8
    wceq
    w3a
    vu
    cA
    wrex
    #
    vx
    cio
    #
    cmpt
    #
    cif
    #
    @17
    nosupbday.1
    @11
    @17
    @33
    iftrue
    syl5eq
    dmeqd
    @14
    @16
    cdm
    #
    cun
    @14
    @14
    csn
    #
    cun
    @18
    @15
    @35
    @36
    @14
    @14
    c2o
    c2o
    con0
    2on
    elexi
    dmsnop
    uneq2i
    @13
    @16
    dmun
    @14
    df-suc
    3eqtr4i
    syl6eq
    adantr
    @12
    @14
    @6
    wss
    #
    @15
    @7
    wss
    #
    @12
    @14
    @5
    wcel
    @37
    @12
    @13
    cbday
    cfv
    #
    @14
    @5
    @12
    @13
    csur
    wcel
    #
    @39
    @14
    wceq
    @12
    cA
    csur
    @13
    @11
    @0
    @1
    simprl
    #
    @12
    @10
    vx
    cA
    wreu
    #
    @13
    cA
    wcel
    #
    @12
    @11
    @10
    vx
    cA
    wrmo
    #
    @42
    @11
    @2
    simpl
    @2
    @44
    @11
    @0
    @44
    @1
    vx
    vy
    cA
    nomaxmo
    adantr
    adantl
    @10
    vx
    cA
    reu5
    sylanbrc
    @10
    vx
    cA
    riotacl
    syl
    #
    sseldd
    #
    @13
    bdayval
    syl
    cbday
    csur
    wfn
    #
    @12
    @0
    @43
    @39
    @5
    wcel
    csur
    con0
    cbday
    wfo
    #
    @47
    bdayfo
    csur
    con0
    cbday
    fofn
    ax-mp
    #
    @41
    @45
    csur
    cA
    cbday
    @13
    fnfvima
    mp3an2i
    eqeltrrd
    @14
    @5
    elssuni
    syl
    @12
    @14
    word
    #
    @6
    word
    #
    @37
    @38
    wb
    @12
    @40
    @50
    @46
    @13
    nodmord
    syl
    @5
    con0
    wss
    @51
    @5
    cbday
    crn
    #
    con0
    cbday
    cA
    imassrn
    @48
    @52
    con0
    wceq
    bdayfo
    csur
    con0
    cbday
    forn
    ax-mp
    sseqtri
    @5
    ssorduni
    ax-mp
    @14
    @6
    ordsucsssuc
    sylancl
    mpbid
    eqsstrd
    @11
    wn
    #
    @2
    wa
    @4
    @28
    @7
    @53
    @4
    @28
    wceq
    @2
    @53
    @4
    @33
    cdm
    @28
    @53
    cS
    @33
    @53
    cS
    @34
    @33
    nosupbday.1
    @11
    @17
    @33
    iffalse
    syl5eq
    dmeqd
    vg
    @28
    @32
    @33
    @31
    vx
    iotaex
    @33
    eqid
    dmmpti
    syl6eq
    adantr
    @2
    @28
    @7
    wss
    @53
    @2
    @27
    vy
    @7
    @2
    @26
    @9
    @7
    wcel
    #
    vu
    cA
    @2
    @19
    cA
    wcel
    #
    wa
    #
    @21
    @54
    @25
    @56
    @20
    @7
    @9
    @56
    @20
    @6
    @7
    @56
    @20
    @5
    wcel
    #
    @20
    @6
    wss
    @0
    @55
    @57
    @1
    @0
    @55
    wa
    #
    @19
    cbday
    cfv
    #
    @20
    @5
    @58
    @19
    csur
    wcel
    @59
    @20
    wceq
    cA
    csur
    @19
    ssel2
    @19
    bdayval
    syl
    @47
    @0
    @55
    @59
    @5
    wcel
    @49
    csur
    cA
    cbday
    @19
    fnfvima
    mp3an1
    eqeltrrd
    adantlr
    @20
    @5
    elssuni
    syl
    @6
    sssucid
    syl6ss
    sseld
    adantrd
    rexlimdva
    abssdv
    adantl
    eqsstrd
    pm2.61ian
    eqsstrd
end
