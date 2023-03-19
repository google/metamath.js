include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "wn.mm"
include "cotp.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "hdmapfval.mm"
include "fveq1d.mm"
include "cvv.mm"
include "riotaex.mm"
include "sneq.mm"
include "fveq2d.mm"
include "uneq2d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "oteq3.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem hdmapval
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  let va: setvar a
  let ve: setvar e
  let vi: setvar i
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  assume hdmapval.h: |- H = ( LHyp ` K )
  assume hdmapfval.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapfval.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapfval.v: |- V = ( Base ` U )
  assume hdmapfval.n: |- N = ( LSpan ` U )
  assume hdmapfval.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapfval.d: |- D = ( Base ` C )
  assume hdmapfval.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapfval.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmapfval.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapfval.k: |- ( ph -> ( K e. A /\ W e. H ) )
  assume hdmapval.t: |- ( ph -> T e. V )

  disjoint y z
  disjoint K y
  disjoint K z
  disjoint D y
  disjoint E y
  disjoint E z
  disjoint I y
  disjoint I z
  disjoint U y
  disjoint U z
  disjoint V y
  disjoint V z
  disjoint W y
  disjoint W z
  disjoint T y
  disjoint T z
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint a e
  disjoint a i
  disjoint a k
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint K a
  disjoint e i
  disjoint e k
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e y
  disjoint e z
  disjoint K e
  disjoint i k
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint K i
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k y
  disjoint k z
  disjoint K k
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint K t
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint K u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint K v
  disjoint w y
  disjoint w z
  disjoint K w
  disjoint D a
  disjoint D e
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint E a
  disjoint E e
  disjoint E t
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint I a
  disjoint I e
  disjoint I i
  disjoint I t
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint J a
  disjoint J e
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint N a
  disjoint N e
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint U t
  disjoint V a
  disjoint V e
  disjoint V t
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint W a
  disjoint W e
  disjoint W i
  disjoint W t
  disjoint W u
  disjoint W v
  disjoint W w
  disjoint D t
  disjoint J t
  disjoint N t
  disjoint T t
  assert |- ( ph -> ( S ` T ) = ( iota_ y e. D A. z e. V ( -. z e. ( ( N ` { E } ) u. ( N ` { T } ) ) -> y = ( I ` <. z , ( I ` <. E , ( J ` E ) , z >. ) , T >. ) ) ) )

  proof
    wph
    cT
    cS
    cfv
    cT
    vt
    cV
    vz
    cv
    #
    cE
    csn
    cN
    cfv
    #
    vt
    cv
    #
    csn
    #
    cN
    cfv
    #
    cun
    #
    wcel
    #
    wn
    #
    vy
    cv
    #
    @0
    cE
    cE
    cJ
    cfv
    @0
    cotp
    cI
    cfv
    #
    @2
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
    crio
    #
    cmpt
    #
    cfv
    #
    @0
    @1
    cT
    csn
    #
    cN
    cfv
    #
    cun
    #
    wcel
    #
    wn
    #
    @8
    @0
    @9
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
    crio
    #
    wph
    cT
    cS
    @16
    wph
    vy
    vz
    vt
    cA
    cC
    cD
    cS
    cU
    cE
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    hdmapval.h
    hdmapfval.e
    hdmapfval.u
    hdmapfval.v
    hdmapfval.n
    hdmapfval.c
    hdmapfval.d
    hdmapfval.j
    hdmapfval.i
    hdmapfval.s
    hdmapfval.k
    hdmapfval
    fveq1d
    wph
    cT
    cV
    wcel
    @28
    cvv
    wcel
    @17
    @28
    wceq
    hdmapval.t
    @27
    vy
    cD
    riotaex
    vt
    cT
    @15
    @28
    cV
    cvv
    @16
    @2
    cT
    wceq
    #
    @14
    @27
    vy
    cD
    @29
    @13
    @26
    vz
    cV
    @29
    @7
    @22
    @12
    @25
    @29
    @6
    @21
    @29
    @5
    @20
    @0
    @29
    @4
    @19
    @1
    @29
    @3
    @18
    cN
    @2
    cT
    sneq
    fveq2d
    uneq2d
    eleq2d
    notbid
    @29
    @11
    @24
    @8
    @29
    @10
    @23
    cI
    @2
    cT
    @0
    @9
    oteq3
    fveq2d
    eqeq2d
    imbi12d
    ralbidv
    riotabidv
    @16
    eqid
    fvmptg
    sylancl
    eqtrd
end
