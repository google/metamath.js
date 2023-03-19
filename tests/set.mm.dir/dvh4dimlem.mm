include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "clsm.mm"
include "co.mm"
include "wss.mm"
include "wn.mm"
include "clsa.mm"
include "wrex.mm"
include "ctp.mm"
include "wcel.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "wne.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lsatlspsn.mm"
include "dvh4dimat.mm"
include "w3a.mm"
include "wceq.mm"
include "clmod.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "islsati.mm"
include "syl2anc.mm"
include "wi.mm"
include "cpr.mm"
include "cun.mm"
include "lsmpr.mm"
include "oveq1d.mm"
include "prssi.mm"
include "snssd.mm"
include "lsmsp2.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "sseq12d.mm"
include "clss.mm"
include "unssd.mm"
include "lspcl.mm"
include "simp3.mm"
include "lspsnel5.mm"
include "bitr4d.mm"
include "df-tp.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "syl6bbr.mm"
include "notbid.mm"
include "biimpd.mm"
include "3exp.mm"
include "com24.mm"
include "a1d.mm"
include "3imp.mm"
include "reximdvai.mm"
include "mpd.mm"
include "rexlimdv3a.mm"

theorem dvh4dimlem
  let wph: wff ph
  let vz: setvar z
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vp: setvar p
  assume dvh3dim.h: |- H = ( LHyp ` K )
  assume dvh3dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dim.v: |- V = ( Base ` U )
  assume dvh3dim.n: |- N = ( LSpan ` U )
  assume dvh3dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh3dim.x: |- ( ph -> X e. V )
  assume dvh4dim.y: |- ( ph -> Y e. V )
  assume dvhdim.z: |- ( ph -> Z e. V )
  assume dvh4dim.o: |- .0. = ( 0g ` U )
  assume dvh4dim.x: |- ( ph -> X =/= .0. )
  assume dvh4dimlem.y: |- ( ph -> Y =/= .0. )
  assume dvh4dimlem.z: |- ( ph -> Z =/= .0. )

  disjoint N z
  disjoint .0. z
  disjoint U z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint Z z
  disjoint ph z
  disjoint K p
  disjoint p z
  disjoint N p
  disjoint .0. p
  disjoint U p
  disjoint V p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  disjoint p ph
  assert |- ( ph -> E. z e. V -. z e. ( N ` { X , Y , Z } ) )

  proof
    wph
    vp
    cv
    #
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cU
    clsm
    cfv
    #
    co
    #
    cZ
    csn
    #
    cN
    cfv
    #
    @3
    co
    #
    wss
    #
    wn
    #
    vp
    cU
    clsa
    cfv
    #
    wrex
    vz
    cv
    #
    cX
    cY
    cZ
    ctp
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vz
    cV
    wrex
    #
    wph
    @10
    @1
    @3
    @2
    @6
    cU
    cH
    cK
    cW
    vp
    dvh3dim.h
    dvh3dim.u
    @3
    eqid
    #
    @10
    eqid
    #
    dvh3dim.k
    wph
    @10
    cN
    cV
    cU
    cX
    c.0
    dvh3dim.v
    dvh3dim.n
    dvh4dim.o
    @18
    wph
    cU
    cH
    cK
    cW
    dvh3dim.h
    dvh3dim.u
    dvh3dim.k
    dvhlmod
    #
    wph
    cX
    cV
    wcel
    #
    cX
    c.0
    wne
    cX
    cV
    c.0
    csn
    cdif
    #
    wcel
    dvh3dim.x
    dvh4dim.x
    cX
    cV
    c.0
    eldifsn
    sylanbrc
    lsatlspsn
    wph
    @10
    cN
    cV
    cU
    cY
    c.0
    dvh3dim.v
    dvh3dim.n
    dvh4dim.o
    @18
    @19
    wph
    cY
    cV
    wcel
    #
    cY
    c.0
    wne
    cY
    @21
    wcel
    dvh4dim.y
    dvh4dimlem.y
    cY
    cV
    c.0
    eldifsn
    sylanbrc
    lsatlspsn
    wph
    @10
    cN
    cV
    cU
    cZ
    c.0
    dvh3dim.v
    dvh3dim.n
    dvh4dim.o
    @18
    @19
    wph
    cZ
    cV
    wcel
    cZ
    c.0
    wne
    cZ
    @21
    wcel
    dvhdim.z
    dvh4dimlem.z
    cZ
    cV
    c.0
    eldifsn
    sylanbrc
    lsatlspsn
    dvh4dimat
    wph
    @9
    @16
    vp
    @10
    wph
    @0
    @10
    wcel
    #
    @9
    w3a
    #
    @0
    @11
    csn
    cN
    cfv
    #
    wceq
    #
    vz
    cV
    wrex
    #
    @16
    @24
    cU
    clmod
    wcel
    #
    @23
    @27
    wph
    @23
    @28
    @9
    @19
    3ad2ant1
    wph
    @23
    @9
    simp2
    vz
    @10
    @0
    cN
    cV
    cU
    clmod
    dvh3dim.v
    dvh3dim.n
    @18
    islsati
    syl2anc
    @24
    @26
    @15
    vz
    cV
    wph
    @23
    @9
    @11
    cV
    wcel
    #
    @26
    @15
    wi
    wi
    #
    wph
    @9
    @30
    wi
    @23
    wph
    @26
    @29
    @9
    @15
    wph
    @26
    @29
    @9
    @15
    wi
    wph
    @26
    @29
    w3a
    #
    @9
    @15
    @31
    @8
    @14
    @31
    @8
    @11
    cX
    cY
    cpr
    #
    @5
    cun
    #
    cN
    cfv
    #
    wcel
    #
    @14
    @31
    @8
    @25
    @34
    wss
    @35
    @31
    @0
    @25
    @7
    @34
    wph
    @26
    @29
    simp2
    @31
    @32
    cN
    cfv
    #
    @6
    @3
    co
    #
    @7
    @34
    @31
    @36
    @4
    @6
    @3
    @31
    @3
    cN
    cV
    cU
    cX
    cY
    dvh3dim.v
    dvh3dim.n
    @17
    wph
    @26
    @28
    @29
    @19
    3ad2ant1
    #
    wph
    @26
    @20
    @29
    dvh3dim.x
    3ad2ant1
    wph
    @26
    @22
    @29
    dvh4dim.y
    3ad2ant1
    lsmpr
    oveq1d
    @31
    @28
    @32
    cV
    wss
    #
    @5
    cV
    wss
    #
    @37
    @34
    wceq
    @38
    wph
    @26
    @39
    @29
    wph
    @20
    @22
    @39
    dvh3dim.x
    dvh4dim.y
    cX
    cY
    cV
    prssi
    syl2anc
    #
    3ad2ant1
    wph
    @26
    @40
    @29
    wph
    cZ
    cV
    dvhdim.z
    snssd
    #
    3ad2ant1
    @3
    @32
    @5
    cN
    cV
    cU
    dvh3dim.v
    dvh3dim.n
    @17
    lsmsp2
    syl3anc
    eqtr3d
    sseq12d
    @31
    cU
    clss
    cfv
    #
    @34
    cN
    cV
    cU
    @11
    dvh3dim.v
    @43
    eqid
    #
    dvh3dim.n
    @38
    wph
    @26
    @34
    @43
    wcel
    #
    @29
    wph
    @28
    @33
    cV
    wss
    @45
    @19
    wph
    @32
    @5
    cV
    @41
    @42
    unssd
    @43
    @33
    cN
    cV
    cU
    dvh3dim.v
    @44
    dvh3dim.n
    lspcl
    syl2anc
    3ad2ant1
    wph
    @26
    @29
    simp3
    lspsnel5
    bitr4d
    @13
    @34
    @11
    @12
    @33
    cN
    cX
    cY
    cZ
    df-tp
    fveq2i
    eleq2i
    syl6bbr
    notbid
    biimpd
    3exp
    com24
    a1d
    3imp
    reximdvai
    mpd
    rexlimdv3a
    mpd
end
