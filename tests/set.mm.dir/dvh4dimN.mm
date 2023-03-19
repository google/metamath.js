include "cv.mm"
include "ctp.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "cpr.mm"
include "dvh3dim.mm"
include "adantr.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "wss.mm"
include "prssi.mm"
include "syl2anc.mm"
include "lspun0.mm"
include "tpeq1.mm"
include "tprot.mm"
include "df-tp.mm"
include "eqtr2i.mm"
include "syl6reqr.mm"
include "fveq2d.mm"
include "sylan9req.mm"
include "eleq2d.mm"
include "notbid.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "tpeq2.mm"
include "tpcomb.mm"
include "eqtr3i.mm"
include "tpeq3.mm"
include "syl6req.mm"
include "wne.mm"
include "w3a.mm"
include "chlt.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "dvh4dimlem.mm"
include "pm2.61da3ne.mm"

theorem dvh4dimN
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
  let cZ: class Z
  let vp: setvar p
  let c.0: class .0.
  assume dvh3dim.h: |- H = ( LHyp ` K )
  assume dvh3dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dim.v: |- V = ( Base ` U )
  assume dvh3dim.n: |- N = ( LSpan ` U )
  assume dvh3dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh3dim.x: |- ( ph -> X e. V )
  assume dvh3dim.y: |- ( ph -> Y e. V )
  assume dvh3dim2.z: |- ( ph -> Z e. V )

  disjoint N z
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
  disjoint .0. z
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
    cX
    cU
    c0g
    cfv
    #
    cY
    @6
    cZ
    @6
    wph
    cX
    @6
    wceq
    #
    wa
    #
    @0
    cY
    cZ
    cpr
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
    @5
    wph
    @13
    @7
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cY
    cZ
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.y
    dvh3dim2.z
    dvh3dim
    adantr
    @8
    @12
    @4
    vz
    cV
    @8
    @11
    @3
    @8
    @10
    @2
    @0
    wph
    @7
    @10
    @9
    @6
    csn
    #
    cun
    #
    cN
    cfv
    @2
    wph
    cN
    cV
    cU
    @9
    @6
    dvh3dim.v
    @6
    eqid
    #
    dvh3dim.n
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
    cY
    cV
    wcel
    #
    cZ
    cV
    wcel
    #
    @9
    cV
    wss
    dvh3dim.y
    dvh3dim2.z
    cY
    cZ
    cV
    prssi
    syl2anc
    lspun0
    @7
    @15
    @1
    cN
    @7
    @1
    @6
    cY
    cZ
    ctp
    #
    @15
    cX
    @6
    cY
    cZ
    tpeq1
    @20
    cY
    cZ
    @6
    ctp
    @15
    @6
    cY
    cZ
    tprot
    cY
    cZ
    @6
    df-tp
    eqtr2i
    syl6reqr
    fveq2d
    sylan9req
    eleq2d
    notbid
    rexbidv
    mpbid
    wph
    cY
    @6
    wceq
    #
    wa
    #
    @0
    cX
    cZ
    cpr
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
    @5
    wph
    @27
    @21
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cZ
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.x
    dvh3dim2.z
    dvh3dim
    adantr
    @22
    @26
    @4
    vz
    cV
    @22
    @25
    @3
    @22
    @24
    @2
    @0
    wph
    @21
    @24
    @23
    @14
    cun
    #
    cN
    cfv
    @2
    wph
    cN
    cV
    cU
    @23
    @6
    dvh3dim.v
    @16
    dvh3dim.n
    @17
    wph
    cX
    cV
    wcel
    #
    @19
    @23
    cV
    wss
    dvh3dim.x
    dvh3dim2.z
    cX
    cZ
    cV
    prssi
    syl2anc
    lspun0
    @21
    @28
    @1
    cN
    @21
    @1
    cX
    @6
    cZ
    ctp
    #
    @28
    cY
    @6
    cX
    cZ
    tpeq2
    cX
    cZ
    @6
    ctp
    @28
    @30
    cX
    cZ
    @6
    df-tp
    cX
    cZ
    @6
    tpcomb
    eqtr3i
    syl6reqr
    fveq2d
    sylan9req
    eleq2d
    notbid
    rexbidv
    mpbid
    wph
    cZ
    @6
    wceq
    #
    wa
    #
    @0
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
    vz
    cV
    wrex
    #
    @5
    wph
    @37
    @31
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
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.x
    dvh3dim.y
    dvh3dim
    adantr
    @32
    @36
    @4
    vz
    cV
    @32
    @35
    @3
    @32
    @34
    @2
    @0
    wph
    @31
    @34
    @33
    @14
    cun
    #
    cN
    cfv
    @2
    wph
    cN
    cV
    cU
    @33
    @6
    dvh3dim.v
    @16
    dvh3dim.n
    @17
    wph
    @29
    @18
    @33
    cV
    wss
    dvh3dim.x
    dvh3dim.y
    cX
    cY
    cV
    prssi
    syl2anc
    lspun0
    @31
    @38
    @1
    cN
    @31
    @1
    cX
    cY
    @6
    ctp
    @38
    cZ
    @6
    cX
    cY
    tpeq3
    cX
    cY
    @6
    df-tp
    syl6req
    fveq2d
    sylan9req
    eleq2d
    notbid
    rexbidv
    mpbid
    wph
    cX
    @6
    wne
    #
    cY
    @6
    wne
    #
    cZ
    @6
    wne
    #
    w3a
    #
    wa
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cY
    @6
    cZ
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @42
    dvh3dim.k
    adantr
    wph
    @29
    @42
    dvh3dim.x
    adantr
    wph
    @18
    @42
    dvh3dim.y
    adantr
    wph
    @19
    @42
    dvh3dim2.z
    adantr
    @16
    wph
    @39
    @40
    @41
    simpr1
    wph
    @39
    @40
    @41
    simpr2
    wph
    @39
    @40
    @41
    simpr3
    dvh4dimlem
    pm2.61da3ne
end
