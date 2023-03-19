include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "wa.mm"
include "wrex.mm"
include "co.mm"
include "wceq.mm"
include "dvh3dim.mm"
include "adantr.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "simpr.mm"
include "lspsnel5a.mm"
include "ssneld.mm"
include "ancld.mm"
include "reximdv.mm"
include "mpd.mm"
include "cbs.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "preq1.mm"
include "prcom.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "lsppr0.mm"
include "sylan9eqr.mm"
include "wss.mm"
include "lspprid2.mm"
include "eqsstrd.mm"
include "lspprid1.mm"
include "jcad.mm"
include "adantlr.mm"
include "wne.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "lssvancl2.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lspsnid.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "sseld.mm"
include "con3dimp.mm"
include "lspsnnecom.mm"
include "lssvancl1.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "pm2.61dane.mm"
include "pm2.61dan.mm"
include "w3a.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lspsnne2.mm"
include "hdmap11lem1.mm"
include "rexlimdv3a.mm"

theorem hdmap11lem2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cS: class S
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vz: setvar z
  assume hdmap11.h: |- H = ( LHyp ` K )
  assume hdmap11.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap11.v: |- V = ( Base ` U )
  assume hdmap11.p: |- .+ = ( +g ` U )
  assume hdmap11.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap11.a: |- .+b = ( +g ` C )
  assume hdmap11.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap11.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap11.x: |- ( ph -> X e. V )
  assume hdmap11.y: |- ( ph -> Y e. V )
  assume hdmap11.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmap11.o: |- .0. = ( 0g ` U )
  assume hdmap11.n: |- N = ( LSpan ` U )
  assume hdmap11.d: |- D = ( Base ` C )
  assume hdmap11.l: |- L = ( LSpan ` C )
  assume hdmap11.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap11.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmap11.i: |- I = ( ( HDMap1 ` K ) ` W )


  assert |- ( ph -> ( S ` ( X .+ Y ) ) = ( ( S ` X ) .+b ( S ` Y ) ) )

  proof
    wph
    vz
    cv
    #
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    @0
    cE
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    #
    wa
    #
    vz
    cV
    wrex
    #
    cX
    cY
    c.pl
    co
    cS
    cfv
    cX
    cS
    cfv
    cY
    cS
    cfv
    c.pb
    co
    wceq
    #
    wph
    cE
    @2
    wcel
    #
    @9
    wph
    @11
    wa
    #
    @4
    vz
    cV
    wrex
    #
    @9
    wph
    @13
    @11
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cY
    hdmap11.h
    hdmap11.u
    hdmap11.v
    hdmap11.n
    hdmap11.k
    hdmap11.x
    hdmap11.y
    dvh3dim
    adantr
    @12
    @4
    @8
    vz
    cV
    @12
    @4
    @7
    @12
    @5
    @2
    @0
    @12
    cU
    clss
    cfv
    #
    @2
    cN
    cU
    cE
    @14
    eqid
    #
    hdmap11.n
    wph
    cU
    clmod
    wcel
    #
    @11
    wph
    cU
    cH
    cK
    cW
    hdmap11.h
    hdmap11.u
    hdmap11.k
    dvhlmod
    #
    adantr
    wph
    @2
    @14
    wcel
    #
    @11
    wph
    @14
    cN
    cV
    cU
    cX
    cY
    hdmap11.v
    @15
    hdmap11.n
    @17
    hdmap11.x
    hdmap11.y
    lspprcl
    #
    adantr
    wph
    @11
    simpr
    lspsnel5a
    ssneld
    ancld
    reximdv
    mpd
    wph
    @11
    wn
    #
    wa
    #
    @9
    cX
    c.0
    wph
    cX
    c.0
    wceq
    #
    @9
    @20
    wph
    @22
    wa
    #
    @0
    cE
    cY
    cpr
    cN
    cfv
    #
    wcel
    wn
    #
    vz
    cV
    wrex
    #
    @9
    wph
    @26
    @22
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cE
    cY
    hdmap11.h
    hdmap11.u
    hdmap11.v
    hdmap11.n
    hdmap11.k
    wph
    cE
    cV
    c.0
    csn
    #
    wph
    cK
    cbs
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cE
    cH
    cK
    cV
    cW
    c.0
    hdmap11.h
    @28
    eqid
    @29
    eqid
    hdmap11.u
    hdmap11.v
    hdmap11.o
    hdmap11.e
    hdmap11.k
    dvheveccl
    eldifad
    #
    hdmap11.y
    dvh3dim
    adantr
    @23
    @25
    @8
    vz
    cV
    @23
    @25
    @4
    @7
    @23
    @2
    @24
    @0
    @23
    @2
    cY
    csn
    cN
    cfv
    #
    @24
    @22
    wph
    @2
    cY
    c.0
    cpr
    #
    cN
    cfv
    @31
    @22
    @1
    @32
    cN
    @22
    @1
    c.0
    cY
    cpr
    @32
    cX
    c.0
    cY
    preq1
    c.0
    cY
    prcom
    syl6eq
    fveq2d
    wph
    cN
    cV
    cU
    cY
    c.0
    hdmap11.v
    hdmap11.o
    hdmap11.n
    @17
    hdmap11.y
    lsppr0
    sylan9eqr
    wph
    @31
    @24
    wss
    @22
    wph
    @14
    @24
    cN
    cU
    cY
    @15
    hdmap11.n
    @17
    wph
    @14
    cN
    cV
    cU
    cE
    cY
    hdmap11.v
    @15
    hdmap11.n
    @17
    @30
    hdmap11.y
    lspprcl
    #
    wph
    cN
    cV
    cU
    cE
    cY
    hdmap11.v
    hdmap11.n
    @17
    @30
    hdmap11.y
    lspprid2
    lspsnel5a
    adantr
    eqsstrd
    ssneld
    @23
    @5
    @24
    @0
    wph
    @5
    @24
    wss
    @22
    wph
    @14
    @24
    cN
    cU
    cE
    @15
    hdmap11.n
    @17
    @33
    wph
    cN
    cV
    cU
    cE
    cY
    hdmap11.v
    hdmap11.n
    @17
    @30
    hdmap11.y
    lspprid1
    lspsnel5a
    adantr
    ssneld
    jcad
    reximdv
    mpd
    adantlr
    @21
    cX
    c.0
    wne
    #
    wa
    #
    cE
    cX
    c.pl
    co
    #
    cV
    wcel
    #
    @36
    @2
    wcel
    #
    wn
    #
    @36
    @5
    wcel
    #
    wn
    #
    @9
    wph
    @37
    @20
    @34
    wph
    @16
    cE
    cV
    wcel
    #
    cX
    cV
    wcel
    #
    @37
    @17
    @30
    hdmap11.x
    c.pl
    cV
    cU
    cE
    cX
    hdmap11.v
    hdmap11.p
    lmodvacl
    syl3anc
    ad2antrr
    @35
    c.pl
    @14
    @2
    cV
    cU
    cX
    cE
    hdmap11.v
    hdmap11.p
    @15
    wph
    @16
    @20
    @34
    @17
    ad2antrr
    #
    wph
    @18
    @20
    @34
    @19
    ad2antrr
    wph
    cX
    @2
    wcel
    @20
    @34
    wph
    cN
    cV
    cU
    cX
    cY
    hdmap11.v
    hdmap11.n
    @17
    hdmap11.x
    hdmap11.y
    lspprid1
    #
    ad2antrr
    wph
    @42
    @20
    @34
    @30
    ad2antrr
    #
    wph
    @20
    @34
    simplr
    lssvancl2
    @35
    c.pl
    @14
    @5
    cV
    cU
    cE
    cX
    hdmap11.v
    hdmap11.p
    @15
    @44
    wph
    @5
    @14
    wcel
    #
    @20
    @34
    wph
    @16
    @42
    @47
    @17
    @30
    @14
    cN
    cV
    cU
    cE
    hdmap11.v
    @15
    hdmap11.n
    lspsncl
    syl2anc
    ad2antrr
    wph
    cE
    @5
    wcel
    #
    @20
    @34
    wph
    @16
    @42
    @48
    @17
    @30
    cN
    cV
    cU
    cE
    hdmap11.v
    hdmap11.n
    lspsnid
    syl2anc
    ad2antrr
    wph
    @43
    @20
    @34
    hdmap11.x
    ad2antrr
    #
    @35
    cN
    cV
    cU
    cE
    cX
    c.0
    hdmap11.v
    hdmap11.o
    hdmap11.n
    wph
    cU
    clvec
    wcel
    @20
    @34
    wph
    cU
    cH
    cK
    cW
    hdmap11.h
    hdmap11.u
    hdmap11.k
    dvhlvec
    ad2antrr
    @46
    @35
    @43
    @34
    cX
    cV
    @27
    cdif
    wcel
    @49
    @21
    @34
    simpr
    cX
    cV
    c.0
    eldifsn
    sylanbrc
    @21
    cE
    cX
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    @34
    wph
    @51
    @11
    wph
    @50
    @2
    cE
    wph
    @14
    @2
    cN
    cU
    cX
    @15
    hdmap11.n
    @17
    @19
    @45
    lspsnel5a
    sseld
    con3dimp
    adantr
    lspsnnecom
    lssvancl1
    @8
    @39
    @41
    wa
    vz
    @36
    cV
    @0
    @36
    wceq
    #
    @4
    @39
    @7
    @41
    @52
    @3
    @38
    @0
    @36
    @2
    eleq1
    notbid
    @52
    @6
    @40
    @0
    @36
    @5
    eleq1
    notbid
    anbi12d
    rspcev
    syl12anc
    pm2.61dane
    pm2.61dan
    wph
    @8
    @10
    vz
    cV
    wph
    @0
    cV
    wcel
    #
    @8
    w3a
    #
    vz
    cC
    cD
    c.pl
    c.pb
    cS
    cU
    cE
    cH
    cI
    cJ
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap11.h
    hdmap11.u
    hdmap11.v
    hdmap11.p
    hdmap11.c
    hdmap11.a
    hdmap11.s
    wph
    @53
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @8
    hdmap11.k
    3ad2ant1
    wph
    @53
    @43
    @8
    hdmap11.x
    3ad2ant1
    wph
    @53
    cY
    cV
    wcel
    @8
    hdmap11.y
    3ad2ant1
    hdmap11.e
    hdmap11.o
    hdmap11.n
    hdmap11.d
    hdmap11.l
    hdmap11.m
    hdmap11.j
    hdmap11.i
    wph
    @53
    @8
    simp2
    #
    wph
    @53
    @4
    @7
    simp3l
    @54
    cN
    cV
    cU
    @0
    cE
    hdmap11.v
    hdmap11.n
    wph
    @53
    @16
    @8
    @17
    3ad2ant1
    @55
    wph
    @53
    @42
    @8
    @30
    3ad2ant1
    wph
    @53
    @4
    @7
    simp3r
    lspsnne2
    hdmap11lem1
    rexlimdv3a
    mpd
end
