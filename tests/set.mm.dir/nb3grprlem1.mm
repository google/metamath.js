include "cnbgr.mm"
include "co.mm"
include "cpr.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "prid1g.mm"
include "3ad2ant2.mm"
include "syl.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2.mm"
include "eqcoms.mm"
include "adantl.mm"
include "mpbid.mm"
include "cusgr.mm"
include "nbusgreledg.mm"
include "prcom.mm"
include "a1i.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "prid2g.mm"
include "3ad2ant3.mm"
include "jca.mm"
include "cv.mm"
include "crab.mm"
include "nbusgr.mm"
include "cab.mm"
include "wo.mm"
include "ctp.mm"
include "wi.mm"
include "w3o.mm"
include "vex.mm"
include "eltp.mm"
include "wne.mm"
include "usgredgne.mm"
include "wn.mm"
include "df-ne.mm"
include "pm2.24.mm"
include "com12.mm"
include "sylbi.mm"
include "ex.mm"
include "com3r.mm"
include "orc.mm"
include "2a1d.mm"
include "olc.mm"
include "3jaoi.mm"
include "sylbid.mm"
include "impd.mm"
include "eqid.mm"
include "3mix2i.mm"
include "simp2d.mm"
include "eltpg.mm"
include "mpbiri.mm"
include "eleq1.mm"
include "bicomd.mm"
include "impcom.mm"
include "preq2.mm"
include "biimpcd.mm"
include "ad2antrl.mm"
include "tpid3g.mm"
include "ad2antll.mm"
include "jaoi.mm"
include "impbid.mm"
include "abbidv.mm"
include "df-rab.mm"
include "dfpr2.mm"
include "3eqtr4g.mm"
include "eqtrd.mm"
include "impbida.mm"

theorem nb3grprlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vv: setvar v
  assume nb3grpr.v: |- V = ( Vtx ` G )
  assume nb3grpr.e: |- E = ( Edg ` G )
  assume nb3grpr.g: |- ( ph -> G e. USGraph )
  assume nb3grpr.t: |- ( ph -> V = { A , B , C } )
  assume nb3grpr.s: |- ( ph -> ( A e. X /\ B e. Y /\ C e. Z ) )


  assert |- ( ph -> ( ( G NeighbVtx A ) = { B , C } <-> ( { A , B } e. E /\ { A , C } e. E ) ) )

  proof
    wph
    cG
    cA
    cnbgr
    co
    #
    cB
    cC
    cpr
    #
    wceq
    #
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cA
    cC
    cpr
    #
    cE
    wcel
    #
    wa
    #
    wph
    @2
    wa
    #
    @4
    @6
    @8
    cB
    @0
    wcel
    #
    @4
    @8
    cB
    @1
    wcel
    #
    @9
    wph
    @10
    @2
    wph
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    w3a
    #
    @10
    nb3grpr.s
    @12
    @11
    @10
    @13
    cB
    cC
    cY
    prid1g
    3ad2ant2
    syl
    adantr
    @2
    @10
    @9
    wb
    #
    wph
    @15
    @1
    @0
    @1
    @0
    cB
    eleq2
    eqcoms
    adantl
    mpbid
    wph
    @9
    @4
    wb
    #
    @2
    wph
    cG
    cusgr
    wcel
    #
    @16
    nb3grpr.g
    @17
    @9
    cB
    cA
    cpr
    #
    cE
    wcel
    @4
    cE
    cG
    cA
    cB
    nb3grpr.e
    nbusgreledg
    @17
    @18
    @3
    cE
    @18
    @3
    wceq
    @17
    cB
    cA
    prcom
    a1i
    eleq1d
    bitrd
    syl
    adantr
    mpbid
    @8
    cC
    @0
    wcel
    #
    @6
    @8
    cC
    @1
    wcel
    #
    @19
    wph
    @20
    @2
    wph
    @14
    @20
    nb3grpr.s
    @13
    @11
    @20
    @12
    cB
    cC
    cZ
    prid2g
    3ad2ant3
    syl
    adantr
    @2
    @20
    @19
    wb
    #
    wph
    @21
    @1
    @0
    @1
    @0
    cC
    eleq2
    eqcoms
    adantl
    mpbid
    wph
    @19
    @6
    wb
    #
    @2
    wph
    @17
    @22
    nb3grpr.g
    @17
    @19
    cC
    cA
    cpr
    #
    cE
    wcel
    @6
    cE
    cG
    cA
    cC
    nb3grpr.e
    nbusgreledg
    @17
    @23
    @5
    cE
    @23
    @5
    wceq
    @17
    cC
    cA
    prcom
    a1i
    eleq1d
    bitrd
    syl
    adantr
    mpbid
    jca
    wph
    @7
    wa
    #
    @0
    cA
    vv
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vv
    cV
    crab
    #
    @1
    wph
    @0
    @28
    wceq
    #
    @7
    wph
    @17
    @29
    nb3grpr.g
    vv
    cE
    cG
    cA
    cV
    nb3grpr.v
    nb3grpr.e
    nbusgr
    syl
    adantr
    @24
    @25
    cV
    wcel
    #
    @27
    wa
    #
    vv
    cab
    @25
    cB
    wceq
    #
    @25
    cC
    wceq
    #
    wo
    #
    vv
    cab
    @28
    @1
    @24
    @31
    @34
    vv
    @24
    @31
    @34
    @24
    @30
    @27
    @34
    @24
    @30
    @25
    cA
    cB
    cC
    ctp
    #
    wcel
    #
    @27
    @34
    wi
    #
    wph
    @30
    @36
    wb
    #
    @7
    wph
    cV
    @35
    wceq
    #
    @38
    nb3grpr.t
    cV
    @35
    @25
    eleq2
    #
    syl
    adantr
    @36
    @24
    @37
    @36
    @25
    cA
    wceq
    #
    @32
    @33
    w3o
    @24
    @37
    wi
    #
    @25
    cA
    cB
    cC
    vv
    vex
    eltp
    @41
    @42
    @32
    @33
    @24
    @27
    @41
    @34
    wph
    @27
    @41
    @34
    wi
    #
    wi
    #
    @7
    wph
    @17
    @44
    nb3grpr.g
    @17
    @27
    @43
    @17
    @27
    wa
    cA
    @25
    wne
    #
    @43
    cE
    cG
    cA
    @25
    nb3grpr.e
    usgredgne
    @45
    cA
    @25
    wceq
    #
    wn
    #
    @43
    cA
    @25
    df-ne
    @41
    @47
    @34
    @47
    @34
    wi
    cA
    @25
    @46
    @34
    pm2.24
    eqcoms
    com12
    sylbi
    syl
    ex
    syl
    adantr
    com3r
    @32
    @34
    @24
    @27
    @32
    @33
    orc
    2a1d
    @33
    @34
    @24
    @27
    @33
    @32
    olc
    2a1d
    3jaoi
    sylbi
    com12
    sylbid
    impd
    @34
    @24
    @31
    @32
    @24
    @31
    wi
    @33
    @32
    @24
    @31
    @32
    @24
    wa
    @30
    @27
    @24
    @32
    @30
    wph
    @32
    @30
    wi
    @7
    wph
    @32
    @30
    wph
    @32
    wa
    #
    @36
    @30
    @48
    cB
    @35
    wcel
    #
    @36
    wph
    @49
    @32
    wph
    @49
    cB
    cA
    wceq
    #
    cB
    cB
    wceq
    #
    cB
    cC
    wceq
    #
    w3o
    #
    @51
    @50
    @52
    cB
    eqid
    3mix2i
    wph
    @12
    @49
    @53
    wb
    wph
    @11
    @12
    @13
    nb3grpr.s
    simp2d
    cB
    cA
    cB
    cC
    cY
    eltpg
    syl
    mpbiri
    adantr
    @32
    @49
    @36
    wb
    wph
    @32
    @36
    @49
    @25
    cB
    @35
    eleq1
    bicomd
    adantl
    mpbid
    wph
    @36
    @30
    wb
    #
    @32
    wph
    @39
    @54
    nb3grpr.t
    @39
    @30
    @36
    @40
    bicomd
    syl
    #
    adantr
    mpbid
    ex
    adantr
    impcom
    @24
    @32
    @27
    @4
    @32
    @27
    wi
    wph
    @6
    @32
    @4
    @27
    @4
    @27
    wb
    cB
    @25
    cB
    @25
    wceq
    @3
    @26
    cE
    cB
    @25
    cA
    preq2
    eleq1d
    eqcoms
    biimpcd
    ad2antrl
    impcom
    jca
    ex
    @33
    @24
    @31
    @33
    @24
    wa
    @30
    @27
    @24
    @33
    @30
    wph
    @33
    @30
    wi
    @7
    wph
    @33
    @30
    wph
    @33
    wa
    #
    @36
    @30
    @56
    cC
    @35
    wcel
    #
    @36
    wph
    @57
    @33
    wph
    @14
    @57
    nb3grpr.s
    @13
    @11
    @57
    @12
    cC
    cZ
    cA
    cB
    tpid3g
    3ad2ant3
    syl
    adantr
    @33
    @57
    @36
    wb
    wph
    @33
    @36
    @57
    @25
    cC
    @35
    eleq1
    bicomd
    adantl
    mpbid
    wph
    @54
    @33
    @55
    adantr
    mpbid
    ex
    adantr
    impcom
    @24
    @33
    @27
    @6
    @33
    @27
    wi
    wph
    @4
    @33
    @6
    @27
    @6
    @27
    wb
    cC
    @25
    cC
    @25
    wceq
    @5
    @26
    cE
    cC
    @25
    cA
    preq2
    eleq1d
    eqcoms
    biimpcd
    ad2antll
    impcom
    jca
    ex
    jaoi
    com12
    impbid
    abbidv
    @27
    vv
    cV
    df-rab
    vv
    cB
    cC
    dfpr2
    3eqtr4g
    eqtrd
    impbida
end
