include "cfv.mm"
include "csn.mm"
include "cmulr.mm"
include "co.mm"
include "cvsca.mm"
include "c0g.mm"
include "wceq.mm"
include "syl5eqr.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "wb.mm"
include "dvhlmod.mm"
include "lduallmod.mm"
include "clfn.mm"
include "eqid.mm"
include "cv.mm"
include "crab.mm"
include "lcfrlem10.mm"
include "ldualelvbase.mm"
include "lcfrlem29.mm"
include "ldualvscl.mm"
include "lmodsubeq0.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "dvhlvec.mm"
include "wne.mm"
include "cdr.mm"
include "clvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "lcfrlem22.mm"
include "lsatssv.mm"
include "sseldd.mm"
include "lflcl.mm"
include "drnginvrn0.mm"
include "drnginvrcl.mm"
include "drngmulne0.mm"
include "mpbir2and.mm"
include "ldualkrsc.mm"
include "eqtrd.mm"
include "lcfrlem14.mm"
include "3eqtr3d.mm"

theorem lcfrlem31
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  assume lcfrlem17.h: |- H = ( LHyp ` K )
  assume lcfrlem17.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem17.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem17.v: |- V = ( Base ` U )
  assume lcfrlem17.p: |- .+ = ( +g ` U )
  assume lcfrlem17.z: |- .0. = ( 0g ` U )
  assume lcfrlem17.n: |- N = ( LSpan ` U )
  assume lcfrlem17.a: |- A = ( LSAtoms ` U )
  assume lcfrlem17.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem17.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lcfrlem17.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lcfrlem17.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lcfrlem22.b: |- B = ( ( N ` { X , Y } ) i^i ( ._|_ ` { ( X .+ Y ) } ) )
  assume lcfrlem24.t: |- .x. = ( .s ` U )
  assume lcfrlem24.s: |- S = ( Scalar ` U )
  assume lcfrlem24.q: |- Q = ( 0g ` S )
  assume lcfrlem24.r: |- R = ( Base ` S )
  assume lcfrlem24.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )
  assume lcfrlem24.ib: |- ( ph -> I e. B )
  assume lcfrlem24.l: |- L = ( LKer ` U )
  assume lcfrlem25.d: |- D = ( LDual ` U )
  assume lcfrlem28.jn: |- ( ph -> ( ( J ` Y ) ` I ) =/= Q )
  assume lcfrlem29.i: |- F = ( invr ` S )
  assume lcfrlem30.m: |- .- = ( -g ` D )
  assume lcfrlem30.c: |- C = ( ( J ` X ) .- ( ( ( F ` ( ( J ` Y ) ` I ) ) ( .r ` S ) ( ( J ` X ) ` I ) ) ( .s ` D ) ( J ` Y ) ) )
  assume lcfrlem31.xi: |- ( ph -> ( ( J ` X ) ` I ) =/= Q )
  assume lcfrlem31.cn: |- ( ph -> C = ( 0g ` D ) )

  disjoint k v
  disjoint k w
  disjoint k x
  disjoint ._|_ k
  disjoint v w
  disjoint v x
  disjoint ._|_ v
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .+ k
  disjoint .+ v
  disjoint .+ w
  disjoint .+ x
  disjoint R k
  disjoint R v
  disjoint R x
  disjoint S k
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .x. x
  disjoint V v
  disjoint V x
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint .0. x
  disjoint J f
  disjoint L f
  disjoint ._|_ f
  disjoint .+ f
  disjoint R f
  disjoint .x. f
  disjoint U f
  disjoint V f
  disjoint X f
  disjoint Y f
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  assert |- ( ph -> ( N ` { X } ) = ( N ` { Y } ) )

  proof
    wph
    cX
    cJ
    cfv
    #
    cL
    cfv
    #
    c.pe
    cfv
    cY
    cJ
    cfv
    #
    cL
    cfv
    #
    c.pe
    cfv
    cX
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    wph
    @1
    @3
    c.pe
    wph
    @1
    cI
    @2
    cfv
    #
    cF
    cfv
    #
    cI
    @0
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    @2
    cD
    cvsca
    cfv
    #
    co
    #
    cL
    cfv
    @3
    wph
    @0
    @10
    cL
    wph
    @0
    @10
    c.mi
    co
    #
    cD
    c0g
    cfv
    #
    wceq
    #
    @0
    @10
    wceq
    #
    wph
    @11
    cC
    @12
    lcfrlem30.c
    lcfrlem31.cn
    syl5eqr
    wph
    cD
    clmod
    wcel
    @0
    cD
    cbs
    cfv
    #
    wcel
    @10
    @15
    wcel
    @13
    @14
    wb
    wph
    cD
    cU
    lcfrlem25.d
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlmod
    #
    lduallmod
    wph
    cD
    cU
    clfn
    cfv
    #
    @0
    @15
    cU
    clmod
    @17
    eqid
    #
    lcfrlem25.d
    @15
    eqid
    #
    @16
    wph
    vx
    vw
    vv
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @20
    wceq
    vf
    @17
    crab
    #
    cD
    c.pl
    @12
    cR
    cS
    c.x
    cU
    vf
    vk
    @17
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @18
    lcfrlem24.l
    lcfrlem25.d
    @12
    eqid
    #
    @21
    eqid
    #
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem10
    #
    ldualelvbase
    wph
    cD
    @17
    @10
    @15
    cU
    clmod
    @18
    lcfrlem25.d
    @19
    @16
    wph
    cD
    cS
    @9
    @17
    @2
    cR
    cU
    @8
    @18
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem25.d
    @9
    eqid
    #
    @16
    wph
    vx
    vw
    vv
    cA
    cB
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vk
    cF
    cH
    cI
    cJ
    cK
    cL
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem24.r
    lcfrlem24.j
    lcfrlem24.ib
    lcfrlem24.l
    lcfrlem25.d
    lcfrlem28.jn
    lcfrlem29.i
    lcfrlem29
    #
    wph
    vx
    vw
    vv
    @21
    cD
    c.pl
    @12
    cR
    cS
    c.x
    cU
    vf
    vk
    @17
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @18
    lcfrlem24.l
    lcfrlem25.d
    @22
    @23
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem10
    #
    ldualvscl
    ldualelvbase
    @0
    @10
    c.mi
    @15
    cD
    @12
    @19
    @22
    lcfrlem30.m
    lmodsubeq0
    syl3anc
    mpbid
    fveq2d
    wph
    cD
    cS
    @9
    @17
    @2
    cR
    cL
    cU
    @8
    cQ
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem24.q
    @18
    lcfrlem24.l
    lcfrlem25.d
    @25
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlvec
    #
    @27
    @26
    wph
    @8
    cQ
    wne
    @5
    cQ
    wne
    #
    @6
    cQ
    wne
    wph
    cS
    cdr
    wcel
    #
    @4
    cR
    wcel
    #
    @4
    cQ
    wne
    #
    @29
    wph
    cU
    clvec
    wcel
    @30
    @28
    cS
    cU
    lcfrlem24.s
    lvecdrng
    syl
    #
    wph
    cU
    clmod
    wcel
    #
    @2
    @17
    wcel
    cI
    cV
    wcel
    #
    @31
    @16
    @27
    wph
    cB
    cV
    cI
    wph
    cA
    cB
    cV
    cU
    lcfrlem17.v
    lcfrlem17.a
    @16
    wph
    cA
    cB
    c.pl
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem22
    lsatssv
    lcfrlem24.ib
    sseldd
    #
    cS
    @17
    @2
    cR
    cV
    cU
    cI
    clmod
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.v
    @18
    lflcl
    syl3anc
    #
    lcfrlem28.jn
    cR
    cS
    cF
    @4
    cQ
    lcfrlem24.r
    lcfrlem24.q
    lcfrlem29.i
    drnginvrn0
    syl3anc
    lcfrlem31.xi
    wph
    cR
    cS
    @7
    @5
    @6
    cQ
    lcfrlem24.r
    lcfrlem24.q
    @7
    eqid
    @33
    wph
    @30
    @31
    @32
    @5
    cR
    wcel
    @33
    @37
    lcfrlem28.jn
    cR
    cS
    cF
    @4
    cQ
    lcfrlem24.r
    lcfrlem24.q
    lcfrlem29.i
    drnginvrcl
    syl3anc
    wph
    @34
    @0
    @17
    wcel
    @35
    @6
    cR
    wcel
    @16
    @24
    @36
    cS
    @17
    @0
    cR
    cV
    cU
    cI
    clmod
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.v
    @18
    lflcl
    syl3anc
    drngmulne0
    mpbir2and
    ldualkrsc
    eqtrd
    fveq2d
    wph
    vx
    vw
    vv
    @21
    cD
    c.pl
    @12
    cR
    cS
    c.x
    cU
    vf
    vk
    @17
    cH
    cJ
    cK
    cL
    cN
    c.pe
    cV
    cW
    cX
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @18
    lcfrlem24.l
    lcfrlem25.d
    @22
    @23
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.n
    lcfrlem14
    wph
    vx
    vw
    vv
    @21
    cD
    c.pl
    @12
    cR
    cS
    c.x
    cU
    vf
    vk
    @17
    cH
    cJ
    cK
    cL
    cN
    c.pe
    cV
    cW
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @18
    lcfrlem24.l
    lcfrlem25.d
    @22
    @23
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem17.n
    lcfrlem14
    3eqtr3d
end
