include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cun.mm"
include "wcel.mm"
include "wn.mm"
include "cotp.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "mapdh9a.mm"
include "wa.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "cdif.mm"
include "simplr.mm"
include "hdmap1valc.mm"
include "oteq2d.mm"
include "fveq2d.mm"
include "elun1.mm"
include "con3i.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "simpr.mm"
include "lssneln0.mm"
include "lspsnne2.mm"
include "necomd.mm"
include "mapdhcl.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "pm5.74da.mm"
include "ralbidva.mm"
include "reubidv.mm"
include "mpbird.mm"

theorem hdmap1eulem
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
  assert |- ( ph -> E! y e. D A. z e. V ( -. z e. ( ( N ` { X } ) u. ( N ` { T } ) ) -> y = ( I ` <. z , ( I ` <. X , F , z >. ) , T >. ) ) )

  proof
    wph
    vz
    cv
    #
    cX
    csn
    cN
    cfv
    #
    cT
    csn
    cN
    cfv
    #
    cun
    wcel
    #
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
    @4
    @5
    @0
    @6
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
    mapdh9a
    wph
    @12
    @18
    vy
    cD
    wph
    @11
    @17
    vz
    cV
    wph
    @0
    cV
    wcel
    #
    wa
    #
    @4
    @10
    @16
    @20
    @4
    wa
    #
    @9
    @15
    @5
    @21
    @9
    @14
    cI
    cfv
    #
    @15
    @21
    @8
    @14
    cI
    @21
    @7
    @13
    @0
    cT
    @21
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
    #
    @19
    @4
    hdmap1eulem.k
    ad2antrr
    wph
    cX
    cV
    c.0
    csn
    #
    cdif
    wcel
    #
    @19
    @4
    hdmap1eulem.x
    ad2antrr
    wph
    cF
    cD
    wcel
    #
    @19
    @4
    hdmap1eulem.f
    ad2antrr
    wph
    @19
    @4
    simplr
    hdmap1eulem.l
    hdmap1valc
    oteq2d
    fveq2d
    @4
    @20
    @0
    @1
    wcel
    #
    wn
    #
    @22
    @15
    wceq
    @27
    @3
    @0
    @1
    @2
    elun1
    con3i
    @20
    @28
    wa
    #
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    @13
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
    wph
    @23
    @19
    @28
    hdmap1eulem.k
    ad2antrr
    #
    @29
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
    @31
    eqid
    #
    wph
    cU
    clmod
    wcel
    #
    @19
    @28
    wph
    cU
    cH
    cK
    cW
    hdmap1eulem.h
    hdmap1eulem.u
    hdmap1eulem.k
    dvhlmod
    ad2antrr
    #
    @29
    @33
    cX
    cV
    wcel
    #
    @1
    @31
    wcel
    @34
    wph
    @35
    @19
    @28
    wph
    cX
    cV
    @24
    hdmap1eulem.x
    eldifad
    ad2antrr
    #
    @31
    cN
    cV
    cU
    cX
    hdmap1eulem.v
    @32
    hdmap1eulem.n
    lspsncl
    syl2anc
    wph
    @19
    @28
    simplr
    #
    @20
    @28
    simpr
    #
    lssneln0
    @29
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
    @30
    wph
    @26
    @19
    @28
    hdmap1eulem.f
    ad2antrr
    wph
    @1
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    @19
    @28
    hdmap1eulem.mn
    ad2antrr
    wph
    @25
    @19
    @28
    hdmap1eulem.x
    ad2antrr
    @37
    @29
    @0
    csn
    cN
    cfv
    @1
    @29
    cN
    cV
    cU
    @0
    cX
    hdmap1eulem.v
    hdmap1eulem.n
    @34
    @37
    @36
    @38
    lspsnne2
    necomd
    mapdhcl
    wph
    cT
    cV
    wcel
    @19
    @28
    hdmap1eulem.y
    ad2antrr
    hdmap1eulem.l
    hdmap1valc
    sylan2
    eqtrd
    eqeq2d
    pm5.74da
    ralbidva
    reubidv
    mpbird
end
