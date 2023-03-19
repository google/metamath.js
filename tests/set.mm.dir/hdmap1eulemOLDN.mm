include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "cotp.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "mapdh9aOLDN.mm"
include "wa.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "csn.mm"
include "cdif.mm"
include "simplr.mm"
include "hdmap1valc.mm"
include "oteq2d.mm"
include "fveq2d.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspprcl.mm"
include "simpr.mm"
include "lssneln0.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "mapdhcl.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "pm5.74da.mm"
include "ralbidva.mm"
include "reubidv.mm"
include "mpbird.mm"

theorem hdmap1eulemOLDN
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume hdmap1eulem.h: |- H = ( LHyp ` K )
  assume hdmap1eulem.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1eulem.v: |- V = ( Base ` U )
  assume hdmap1eulem.s: |- .- = ( -g ` U )
  assume hdmap1eulem.o: |- .0. = ( 0g ` U )
  assume hdmap1eulem.n: |- N = ( LSpan ` U )
  assume hdmap1eulem.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1eulem.d: |- D = ( Base ` C )
  assume hdmap1eulem.r: |- R = ( -g ` C )
  assume hdmap1eulem.q: |- Q = ( 0g ` C )
  assume hdmap1eulem.j: |- J = ( LSpan ` C )
  assume hdmap1eulem.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1eulem.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1eulem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1eulem.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume hdmap1eulem.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1eulem.f: |- ( ph -> F e. D )
  assume hdmap1eulem.y: |- ( ph -> T e. V )
  assume hdmap1eulem.l: |- L = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )

  disjoint C h
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint D h
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint F h
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint J h
  disjoint J x
  disjoint L h
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint M h
  disjoint M x
  disjoint N h
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint .0. h
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint Q x
  disjoint R h
  disjoint R x
  disjoint .- h
  disjoint .- x
  disjoint T h
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U h
  disjoint U z
  disjoint V h
  disjoint V y
  disjoint V z
  disjoint X h
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint h ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> E! y e. D A. z e. V ( -. z e. ( N ` { X , T } ) -> y = ( I ` <. z , ( I ` <. X , F , z >. ) , T >. ) ) )

  proof
    wph
    vz
    cv
    #
    cX
    cT
    cpr
    cN
    cfv
    #
    wcel
    wn
    #
    vy
    cv
    #
    @0
    cX
    cF
    @0
    cotp
    #
    cI
    cfv
    #
    cT
    cotp
    #
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
    vy
    cD
    wreu
    @2
    @3
    @0
    @4
    cL
    cfv
    #
    cT
    cotp
    #
    cL
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
    vy
    cD
    wreu
    wph
    vx
    vy
    vz
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    cF
    cH
    cL
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    c.0
    hdmap1eulem.h
    hdmap1eulem.u
    hdmap1eulem.v
    hdmap1eulem.s
    hdmap1eulem.o
    hdmap1eulem.n
    hdmap1eulem.c
    hdmap1eulem.d
    hdmap1eulem.r
    hdmap1eulem.q
    hdmap1eulem.j
    hdmap1eulem.m
    hdmap1eulem.l
    hdmap1eulem.k
    hdmap1eulem.f
    hdmap1eulem.mn
    hdmap1eulem.x
    hdmap1eulem.y
    mapdh9aOLDN
    wph
    @10
    @16
    vy
    cD
    wph
    @9
    @15
    vz
    cV
    wph
    @0
    cV
    wcel
    #
    wa
    #
    @2
    @8
    @14
    @18
    @2
    wa
    #
    @7
    @13
    @3
    @19
    @7
    @12
    cI
    cfv
    @13
    @19
    @6
    @12
    cI
    @19
    @5
    @11
    @0
    cT
    @19
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cH
    cI
    cJ
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    @0
    c.0
    hdmap1eulem.h
    hdmap1eulem.u
    hdmap1eulem.v
    hdmap1eulem.s
    hdmap1eulem.o
    hdmap1eulem.n
    hdmap1eulem.c
    hdmap1eulem.d
    hdmap1eulem.r
    hdmap1eulem.q
    hdmap1eulem.j
    hdmap1eulem.m
    hdmap1eulem.i
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @17
    @2
    hdmap1eulem.k
    ad2antrr
    #
    wph
    cX
    cV
    c.0
    csn
    #
    cdif
    wcel
    @17
    @2
    hdmap1eulem.x
    ad2antrr
    #
    wph
    cF
    cD
    wcel
    @17
    @2
    hdmap1eulem.f
    ad2antrr
    #
    wph
    @17
    @2
    simplr
    #
    hdmap1eulem.l
    hdmap1valc
    oteq2d
    fveq2d
    @19
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    @11
    cH
    cI
    cJ
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    @0
    cT
    c.0
    hdmap1eulem.h
    hdmap1eulem.u
    hdmap1eulem.v
    hdmap1eulem.s
    hdmap1eulem.o
    hdmap1eulem.n
    hdmap1eulem.c
    hdmap1eulem.d
    hdmap1eulem.r
    hdmap1eulem.q
    hdmap1eulem.j
    hdmap1eulem.m
    hdmap1eulem.i
    @20
    @19
    cU
    clss
    cfv
    #
    @1
    cV
    cU
    @0
    c.0
    hdmap1eulem.v
    hdmap1eulem.o
    @25
    eqid
    #
    wph
    cU
    clmod
    wcel
    @17
    @2
    wph
    cU
    cH
    cK
    cW
    hdmap1eulem.h
    hdmap1eulem.u
    hdmap1eulem.k
    dvhlmod
    #
    ad2antrr
    wph
    @1
    @25
    wcel
    @17
    @2
    wph
    @25
    cN
    cV
    cU
    cX
    cT
    hdmap1eulem.v
    @26
    hdmap1eulem.n
    @27
    wph
    cX
    cV
    @21
    hdmap1eulem.x
    eldifad
    #
    hdmap1eulem.y
    lspprcl
    ad2antrr
    @24
    @18
    @2
    simpr
    #
    lssneln0
    @19
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cH
    cL
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    @0
    c.0
    hdmap1eulem.q
    hdmap1eulem.l
    hdmap1eulem.h
    hdmap1eulem.m
    hdmap1eulem.u
    hdmap1eulem.v
    hdmap1eulem.s
    hdmap1eulem.o
    hdmap1eulem.n
    hdmap1eulem.c
    hdmap1eulem.d
    hdmap1eulem.r
    hdmap1eulem.j
    @20
    @23
    wph
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    @17
    @2
    hdmap1eulem.mn
    ad2antrr
    @22
    @24
    @19
    @0
    csn
    cN
    cfv
    #
    @30
    @19
    @31
    @30
    wne
    @31
    cT
    csn
    cN
    cfv
    wne
    @19
    cN
    cV
    cU
    @0
    cX
    cT
    hdmap1eulem.v
    hdmap1eulem.n
    wph
    cU
    clvec
    wcel
    @17
    @2
    wph
    cU
    cH
    cK
    cW
    hdmap1eulem.h
    hdmap1eulem.u
    hdmap1eulem.k
    dvhlvec
    ad2antrr
    @24
    wph
    cX
    cV
    wcel
    @17
    @2
    @28
    ad2antrr
    wph
    cT
    cV
    wcel
    @17
    @2
    hdmap1eulem.y
    ad2antrr
    #
    @29
    lspindpi
    simpld
    necomd
    mapdhcl
    @32
    hdmap1eulem.l
    hdmap1valc
    eqtrd
    eqeq2d
    pm5.74da
    ralbidva
    reubidv
    mpbird
end
