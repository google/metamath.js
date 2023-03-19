include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "wn.mm"
include "cotp.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "chlt.mm"
include "hdmapval.mm"
include "eqeq1d.mm"
include "wreu.mm"
include "wb.mm"
include "clspn.mm"
include "cmpd.mm"
include "c0g.mm"
include "eqid.mm"
include "cbs.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "mapdhvmap.mm"
include "hvmapcl2.mm"
include "eldifad.mm"
include "hdmap1eu.mm"
include "nfv.mm"
include "nfcvd.mm"
include "nfvd.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "adantl.mm"
include "riota2df.mm"
include "mpdan.mm"
include "bitr4d.mm"

theorem hdmapval2lem
  let wph: wff ph
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let vh: setvar h
  assume hdmapval2.h: |- H = ( LHyp ` K )
  assume hdmapval2.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapval2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapval2.v: |- V = ( Base ` U )
  assume hdmapval2.n: |- N = ( LSpan ` U )
  assume hdmapval2.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapval2.d: |- D = ( Base ` C )
  assume hdmapval2.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapval2.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmapval2.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapval2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapval2.t: |- ( ph -> T e. V )
  assume hdmapval2.f: |- ( ph -> F e. D )

  disjoint C z
  disjoint D z
  disjoint E z
  disjoint F z
  disjoint I z
  disjoint J z
  disjoint K z
  disjoint N z
  disjoint T z
  disjoint U z
  disjoint V z
  disjoint W z
  disjoint ph z
  disjoint h z
  disjoint C h
  disjoint D h
  disjoint E h
  disjoint F h
  disjoint I h
  disjoint J h
  disjoint K h
  disjoint N h
  disjoint T h
  disjoint U h
  disjoint V h
  disjoint W h
  disjoint h ph
  assert |- ( ph -> ( ( S ` T ) = F <-> A. z e. V ( -. z e. ( ( N ` { E } ) u. ( N ` { T } ) ) -> F = ( I ` <. z , ( I ` <. E , ( J ` E ) , z >. ) , T >. ) ) ) )

  proof
    wph
    cT
    cS
    cfv
    #
    cF
    wceq
    vz
    cv
    #
    cE
    csn
    cN
    cfv
    cT
    csn
    cN
    cfv
    cun
    wcel
    wn
    #
    vh
    cv
    #
    @1
    cE
    cE
    cJ
    cfv
    #
    @1
    cotp
    cI
    cfv
    cT
    cotp
    cI
    cfv
    #
    wceq
    #
    wi
    #
    vz
    cV
    wral
    #
    vh
    cD
    crio
    #
    cF
    wceq
    #
    @2
    cF
    @5
    wceq
    #
    wi
    #
    vz
    cV
    wral
    #
    wph
    @0
    @9
    cF
    wph
    vh
    vz
    chlt
    cC
    cD
    cS
    cT
    cU
    cE
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    hdmapval2.h
    hdmapval2.e
    hdmapval2.u
    hdmapval2.v
    hdmapval2.n
    hdmapval2.c
    hdmapval2.d
    hdmapval2.j
    hdmapval2.i
    hdmapval2.s
    hdmapval2.k
    hdmapval2.t
    hdmapval
    eqeq1d
    wph
    @8
    vh
    cD
    wreu
    @13
    @10
    wb
    wph
    vh
    vz
    cC
    cD
    cT
    cU
    @4
    cH
    cI
    cK
    cC
    clspn
    cfv
    #
    cW
    cK
    cmpd
    cfv
    cfv
    #
    cN
    cV
    cW
    cE
    cU
    c0g
    cfv
    #
    hdmapval2.h
    hdmapval2.u
    hdmapval2.v
    @16
    eqid
    #
    hdmapval2.n
    hdmapval2.c
    hdmapval2.d
    @14
    eqid
    #
    @15
    eqid
    #
    hdmapval2.i
    hdmapval2.k
    wph
    cC
    cJ
    cU
    cH
    @14
    cK
    @15
    cN
    cV
    cW
    cE
    @16
    hdmapval2.h
    hdmapval2.u
    hdmapval2.v
    @17
    hdmapval2.n
    hdmapval2.c
    @18
    @19
    hdmapval2.j
    hdmapval2.k
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
    @16
    hdmapval2.h
    @20
    eqid
    @21
    eqid
    hdmapval2.u
    hdmapval2.v
    @17
    hdmapval2.e
    hdmapval2.k
    dvheveccl
    #
    mapdhvmap
    @22
    wph
    @4
    cD
    cC
    c0g
    cfv
    #
    csn
    wph
    cC
    cU
    cD
    cH
    cK
    cJ
    @23
    cV
    cW
    cE
    @16
    hdmapval2.h
    hdmapval2.u
    hdmapval2.v
    @17
    hdmapval2.c
    hdmapval2.d
    @23
    eqid
    hdmapval2.j
    hdmapval2.k
    @22
    hvmapcl2
    eldifad
    hdmapval2.t
    hdmap1eu
    wph
    @8
    @13
    vh
    cD
    cF
    wph
    vh
    nfv
    wph
    vh
    cF
    nfcvd
    wph
    @13
    vh
    nfvd
    hdmapval2.f
    @3
    cF
    wceq
    #
    @8
    @13
    wb
    wph
    @24
    @7
    @12
    vz
    cV
    @24
    @6
    @11
    @2
    @3
    cF
    @5
    eqeq1
    imbi2d
    ralbidv
    adantl
    riota2df
    mpdan
    bitr4d
end
