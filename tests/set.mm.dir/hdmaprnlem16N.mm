include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "wcel.mm"
include "ccnv.mm"
include "clmod.mm"
include "clsa.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lcdlmod.mm"
include "lsatlspsn.mm"
include "mapdcnvatN.mm"
include "islsati.mm"
include "syl2anc.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "clss.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "mapdrn2.mm"
include "eleqtrrd.mm"
include "mapdcnvid2.mm"
include "eqtr3d.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "simp2.mm"
include "simp3.mm"
include "hdmaprnlem15N.mm"
include "rexlimdv3a.mm"

theorem hdmaprnlem16N
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vv: setvar v
  assume hdmaprnlem15.h: |- H = ( LHyp ` K )
  assume hdmaprnlem15.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaprnlem15.v: |- V = ( Base ` U )
  assume hdmaprnlem15.n: |- N = ( LSpan ` U )
  assume hdmaprnlem15.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmaprnlem15.d: |- D = ( Base ` C )
  assume hdmaprnlem15.q: |- .0. = ( 0g ` C )
  assume hdmaprnlem15.l: |- L = ( LSpan ` C )
  assume hdmaprnlem15.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmaprnlem15.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaprnlem15.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaprnlem16.se: |- ( ph -> s e. ( D \ { .0. } ) )


  assert |- ( ph -> s e. ran S )

  proof
    wph
    vv
    cv
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    vs
    cv
    #
    csn
    cL
    cfv
    #
    wceq
    #
    vv
    cV
    wrex
    #
    @3
    cS
    crn
    wcel
    #
    wph
    @4
    cM
    ccnv
    cfv
    #
    @1
    wceq
    #
    vv
    cV
    wrex
    #
    @6
    wph
    cU
    clmod
    wcel
    @8
    cU
    clsa
    cfv
    #
    wcel
    @10
    wph
    cU
    cH
    cK
    cW
    hdmaprnlem15.h
    hdmaprnlem15.u
    hdmaprnlem15.k
    dvhlmod
    wph
    @11
    cC
    clsa
    cfv
    #
    cC
    @4
    cU
    cH
    cK
    cM
    cW
    hdmaprnlem15.h
    hdmaprnlem15.m
    hdmaprnlem15.u
    @11
    eqid
    #
    hdmaprnlem15.c
    @12
    eqid
    #
    hdmaprnlem15.k
    wph
    @12
    cL
    cD
    cC
    @3
    c.0
    hdmaprnlem15.d
    hdmaprnlem15.l
    hdmaprnlem15.q
    @14
    wph
    cC
    cH
    cK
    cW
    hdmaprnlem15.h
    hdmaprnlem15.c
    hdmaprnlem15.k
    lcdlmod
    #
    hdmaprnlem16.se
    lsatlspsn
    mapdcnvatN
    vv
    @11
    @8
    cN
    cV
    cU
    clmod
    hdmaprnlem15.v
    hdmaprnlem15.n
    @13
    islsati
    syl2anc
    wph
    @9
    @5
    vv
    cV
    wph
    @0
    cV
    wcel
    #
    wa
    #
    @9
    @5
    @17
    @9
    wa
    #
    @8
    cM
    cfv
    @2
    @4
    @18
    @8
    @1
    cM
    @17
    @9
    simpr
    fveq2d
    @18
    cH
    cK
    cM
    cW
    @4
    hdmaprnlem15.h
    hdmaprnlem15.m
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @16
    @9
    hdmaprnlem15.k
    ad2antrr
    wph
    @4
    cM
    crn
    #
    wcel
    @16
    @9
    wph
    @4
    cC
    clss
    cfv
    #
    @20
    wph
    cC
    clmod
    wcel
    @3
    cD
    wcel
    @4
    @21
    wcel
    @15
    wph
    @3
    cD
    c.0
    csn
    #
    hdmaprnlem16.se
    eldifad
    @21
    cL
    cD
    cC
    @3
    hdmaprnlem15.d
    @21
    eqid
    #
    hdmaprnlem15.l
    lspsncl
    syl2anc
    wph
    cC
    @21
    cH
    cK
    cM
    cW
    hdmaprnlem15.h
    hdmaprnlem15.m
    hdmaprnlem15.c
    @23
    hdmaprnlem15.k
    mapdrn2
    eleqtrrd
    ad2antrr
    mapdcnvid2
    eqtr3d
    ex
    reximdva
    mpd
    wph
    @5
    @7
    vv
    cV
    wph
    @16
    @5
    w3a
    vv
    cC
    cD
    cS
    cU
    cH
    cK
    cL
    cM
    cN
    cV
    cW
    c.0
    vs
    hdmaprnlem15.h
    hdmaprnlem15.u
    hdmaprnlem15.v
    hdmaprnlem15.n
    hdmaprnlem15.c
    hdmaprnlem15.d
    hdmaprnlem15.q
    hdmaprnlem15.l
    hdmaprnlem15.m
    hdmaprnlem15.s
    wph
    @16
    @19
    @5
    hdmaprnlem15.k
    3ad2ant1
    wph
    @16
    @3
    cD
    @22
    cdif
    wcel
    @5
    hdmaprnlem16.se
    3ad2ant1
    wph
    @16
    @5
    simp2
    wph
    @16
    @5
    simp3
    hdmaprnlem15N
    rexlimdv3a
    mpd
end
