include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "chlt.mm"
include "wss.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "csn.mm"
include "clspn.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "dochlss.mm"
include "simpr.mm"
include "lspsnel5.mm"
include "cdih.mm"
include "crn.mm"
include "dihlsprn.mm"
include "dochcl.mm"
include "dochord.mm"
include "snssd.mm"
include "dochocsp.mm"
include "sseq2d.mm"
include "dochsscl.mm"
include "bitr4d.mm"
include "3bitrd.mm"
include "dfss3.mm"
include "syl6bb.mm"
include "ad2antrr.mm"
include "sselda.mm"
include "simplr.mm"
include "hdmapellkr.mm"
include "dochsncom.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"

theorem hdmapoc
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume hdmapoc.h: |- H = ( LHyp ` K )
  assume hdmapoc.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapoc.v: |- V = ( Base ` U )
  assume hdmapoc.r: |- R = ( Scalar ` U )
  assume hdmapoc.z: |- .0. = ( 0g ` R )
  assume hdmapoc.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapoc.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapoc.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapoc.x: |- ( ph -> X C_ V )

  disjoint y z
  disjoint O y
  disjoint O z
  disjoint V z
  disjoint X y
  disjoint X z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( O ` X ) = { y e. V | A. z e. X ( ( S ` z ) ` y ) = .0. } )

  proof
    wph
    cX
    cO
    cfv
    #
    vy
    cv
    #
    cV
    wcel
    #
    @1
    vz
    cv
    #
    cS
    cfv
    cfv
    c.0
    wceq
    #
    vz
    cX
    wral
    #
    wa
    #
    vy
    cab
    @5
    vy
    cV
    crab
    wph
    @6
    vy
    @0
    wph
    @1
    @0
    wcel
    #
    @2
    @7
    wa
    @6
    wph
    @7
    @2
    wph
    @0
    cV
    @1
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    @0
    cV
    wss
    hdmapoc.k
    hdmapoc.x
    cU
    cH
    cK
    cO
    cV
    cW
    cX
    hdmapoc.h
    hdmapoc.u
    hdmapoc.v
    hdmapoc.o
    dochssv
    syl2anc
    sseld
    pm4.71rd
    wph
    @2
    @7
    @5
    wph
    @2
    wa
    #
    @7
    @3
    @1
    csn
    #
    cO
    cfv
    #
    wcel
    #
    vz
    cX
    wral
    #
    @5
    @10
    @7
    cX
    @12
    wss
    #
    @14
    @10
    @7
    @11
    cU
    clspn
    cfv
    #
    cfv
    #
    @0
    wss
    @0
    cO
    cfv
    #
    @17
    cO
    cfv
    #
    wss
    #
    @15
    @10
    cU
    clss
    cfv
    #
    @0
    @16
    cV
    cU
    @1
    hdmapoc.v
    @21
    eqid
    #
    @16
    eqid
    #
    wph
    cU
    clmod
    wcel
    @2
    wph
    cU
    cH
    cK
    cW
    hdmapoc.h
    hdmapoc.u
    hdmapoc.k
    dvhlmod
    adantr
    wph
    @0
    @21
    wcel
    #
    @2
    wph
    @8
    @9
    @24
    hdmapoc.k
    hdmapoc.x
    @21
    cU
    cH
    cK
    cO
    cV
    cW
    cX
    hdmapoc.h
    hdmapoc.u
    hdmapoc.v
    @22
    hdmapoc.o
    dochlss
    syl2anc
    adantr
    wph
    @2
    simpr
    #
    lspsnel5
    @10
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    cK
    cO
    cW
    @17
    @0
    hdmapoc.h
    @26
    eqid
    #
    hdmapoc.o
    wph
    @8
    @2
    hdmapoc.k
    adantr
    #
    @10
    @8
    @2
    @17
    @26
    crn
    #
    wcel
    @28
    @25
    cU
    cH
    @26
    cK
    @16
    cV
    cW
    @1
    hdmapoc.h
    hdmapoc.u
    hdmapoc.v
    @23
    @27
    dihlsprn
    syl2anc
    wph
    @0
    @29
    wcel
    #
    @2
    wph
    @8
    @9
    @30
    hdmapoc.k
    hdmapoc.x
    cU
    cH
    @26
    cK
    cO
    cV
    cW
    cX
    hdmapoc.h
    @27
    hdmapoc.u
    hdmapoc.v
    hdmapoc.o
    dochcl
    syl2anc
    adantr
    dochord
    @10
    @20
    @18
    @12
    wss
    @15
    @10
    @19
    @12
    @18
    @10
    cU
    cH
    cK
    @16
    cO
    cV
    cW
    @11
    hdmapoc.h
    hdmapoc.u
    hdmapoc.o
    hdmapoc.v
    @23
    @28
    @10
    @1
    cV
    @25
    snssd
    #
    dochocsp
    sseq2d
    @10
    cU
    cH
    @26
    cK
    cO
    cV
    cW
    cX
    @12
    hdmapoc.h
    hdmapoc.u
    hdmapoc.v
    @27
    hdmapoc.o
    @28
    wph
    @9
    @2
    hdmapoc.x
    adantr
    #
    @10
    @8
    @11
    cV
    wss
    @12
    @29
    wcel
    @28
    @31
    cU
    cH
    @26
    cK
    cO
    cV
    cW
    @11
    hdmapoc.h
    @27
    hdmapoc.u
    hdmapoc.v
    hdmapoc.o
    dochcl
    syl2anc
    dochsscl
    bitr4d
    3bitrd
    vz
    cX
    @12
    dfss3
    syl6bb
    @10
    @4
    @13
    vz
    cX
    @10
    @3
    cX
    wcel
    #
    wa
    #
    @4
    @1
    @3
    csn
    cO
    cfv
    wcel
    @13
    @34
    cR
    cS
    cU
    cH
    cK
    cO
    cV
    cW
    @3
    @1
    c.0
    hdmapoc.h
    hdmapoc.o
    hdmapoc.u
    hdmapoc.v
    hdmapoc.r
    hdmapoc.z
    hdmapoc.s
    wph
    @8
    @2
    @33
    hdmapoc.k
    ad2antrr
    #
    @10
    cX
    cV
    @3
    @32
    sselda
    #
    wph
    @2
    @33
    simplr
    #
    hdmapellkr
    @34
    cU
    cH
    cK
    cO
    cV
    cW
    @1
    @3
    hdmapoc.h
    hdmapoc.o
    hdmapoc.u
    hdmapoc.v
    @35
    @37
    @36
    dochsncom
    bitrd
    ralbidva
    bitr4d
    pm5.32da
    bitrd
    abbi2dv
    @5
    vy
    cV
    df-rab
    syl6eqr
end
