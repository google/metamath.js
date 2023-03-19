include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "sneq.mm"
include "fveq2d.mm"
include "sylan9eq.mm"
include "mapd0.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "lspsn0.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "ex.mm"
include "clss.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsssn0.mm"
include "mapd11.mm"
include "wb.mm"
include "lspsneq0.mm"
include "bitrd.mm"
include "sylibd.mm"
include "necon3d.mm"
include "mpd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"

theorem mapdn0
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume mapdindp.h: |- H = ( LHyp ` K )
  assume mapdindp.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdindp.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdindp.v: |- V = ( Base ` U )
  assume mapdindp.n: |- N = ( LSpan ` U )
  assume mapdindp.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdindp.d: |- D = ( Base ` C )
  assume mapdindp.j: |- J = ( LSpan ` C )
  assume mapdindp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdindp.f: |- ( ph -> F e. D )
  assume mapdindp.mx: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdn0.o: |- .0. = ( 0g ` U )
  assume mapdn0.z: |- Z = ( 0g ` C )
  assume mapdn0.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> F e. ( D \ { Z } ) )

  proof
    wph
    cF
    cD
    wcel
    cF
    cZ
    wne
    #
    cF
    cD
    cZ
    csn
    #
    cdif
    wcel
    mapdindp.f
    wph
    cX
    c.0
    wne
    #
    @0
    wph
    cX
    cV
    c.0
    csn
    #
    cdif
    wcel
    @2
    mapdn0.x
    cX
    cV
    c.0
    eldifsni
    syl
    wph
    cF
    cZ
    cX
    c.0
    wph
    cF
    cZ
    wceq
    #
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    @3
    cM
    cfv
    #
    wceq
    #
    cX
    c.0
    wceq
    #
    wph
    @4
    @8
    wph
    @4
    wa
    @6
    @1
    cJ
    cfv
    #
    @7
    wph
    @4
    @6
    cF
    csn
    #
    cJ
    cfv
    @10
    mapdindp.mx
    @4
    @11
    @1
    cJ
    cF
    cZ
    sneq
    fveq2d
    sylan9eq
    wph
    @7
    @10
    wceq
    @4
    wph
    @7
    @1
    @10
    wph
    cC
    cU
    cH
    cK
    cM
    c.0
    cW
    cZ
    mapdindp.h
    mapdindp.m
    mapdindp.u
    mapdn0.o
    mapdindp.c
    mapdn0.z
    mapdindp.k
    mapd0
    wph
    cC
    clmod
    wcel
    @10
    @1
    wceq
    wph
    cC
    cH
    cK
    cW
    mapdindp.h
    mapdindp.c
    mapdindp.k
    lcdlmod
    cJ
    cC
    cZ
    mapdn0.z
    mapdindp.j
    lspsn0
    syl
    eqtr4d
    adantr
    eqtr4d
    ex
    wph
    @8
    @5
    @3
    wceq
    #
    @9
    wph
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    cM
    cW
    @5
    @3
    mapdindp.h
    mapdindp.u
    @13
    eqid
    #
    mapdindp.m
    mapdindp.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @5
    @13
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdindp.h
    mapdindp.u
    mapdindp.k
    dvhlmod
    #
    wph
    cX
    cV
    @3
    mapdn0.x
    eldifad
    #
    @13
    cN
    cV
    cU
    cX
    mapdindp.v
    @14
    mapdindp.n
    lspsncl
    syl2anc
    wph
    @15
    @3
    @13
    wcel
    @17
    @13
    cU
    c.0
    mapdn0.o
    @14
    lsssn0
    syl
    mapd11
    wph
    @15
    @16
    @12
    @9
    wb
    @17
    @18
    cN
    cV
    cU
    cX
    c.0
    mapdindp.v
    mapdn0.o
    mapdindp.n
    lspsneq0
    syl2anc
    bitrd
    sylibd
    necon3d
    mpd
    cF
    cD
    cZ
    eldifsn
    sylanbrc
end
