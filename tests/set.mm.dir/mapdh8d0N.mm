include "cv.mm"
include "cotp.mm"
include "cfv.mm"
include "csn.mm"
include "eldifad.mm"
include "wne.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "mapdhcl.mm"
include "eqeltrrd.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "mapdheq.mm"
include "mpbid.mm"
include "mapdh8a.mm"
include "mapdh8b.mm"
include "eqidd.mm"
include "mapdh8c.mm"
include "eqtr3d.mm"

theorem mapdh8d0N
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cE: class E
  let cZ: class Z
  assume mapdh8a.h: |- H = ( LHyp ` K )
  assume mapdh8a.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh8a.v: |- V = ( Base ` U )
  assume mapdh8a.s: |- .- = ( -g ` U )
  assume mapdh8a.o: |- .0. = ( 0g ` U )
  assume mapdh8a.n: |- N = ( LSpan ` U )
  assume mapdh8a.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh8a.d: |- D = ( Base ` C )
  assume mapdh8a.r: |- R = ( -g ` C )
  assume mapdh8a.q: |- Q = ( 0g ` C )
  assume mapdh8a.j: |- J = ( LSpan ` C )
  assume mapdh8a.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh8a.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh8a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdh8d.f: |- ( ph -> F e. D )
  assume mapdh8d.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8b.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8d.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8d.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8d.xt: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8d.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { T } ) )
  assume mapdh8d.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh8d.wt: |- ( ph -> ( N ` { w } ) =/= ( N ` { T } ) )
  assume mapdh8d.ut: |- ( ph -> ( N ` { X } ) =/= ( N ` { T } ) )
  assume mapdh8d.vw: |- ( ph -> ( N ` { Y } ) =/= ( N ` { w } ) )
  assume mapdh8d.xn: |- ( ph -> -. X e. ( N ` { Y , w } ) )
  assume mapdh8d0.e: |- ( ph -> X e. ( N ` { Y , T } ) )

  disjoint h x
  disjoint .- h
  disjoint .- x
  disjoint .0. h
  disjoint .0. x
  disjoint C h
  disjoint D h
  disjoint D x
  disjoint F h
  disjoint F x
  disjoint I h
  disjoint G h
  disjoint G x
  disjoint J h
  disjoint J x
  disjoint M h
  disjoint M x
  disjoint N h
  disjoint N x
  disjoint h ph
  disjoint R h
  disjoint R x
  disjoint Q x
  disjoint T h
  disjoint T x
  disjoint U h
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint h w
  disjoint w x
  disjoint I x
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. X , F , T >. ) )

  proof
    wph
    vw
    cv
    #
    cX
    cF
    @0
    cotp
    cI
    cfv
    #
    cT
    cotp
    cI
    cfv
    cY
    cG
    cT
    cotp
    cI
    cfv
    cX
    cF
    cT
    cotp
    cI
    cfv
    wph
    vx
    vw
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    @1
    cG
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.q
    mapdh8a.j
    mapdh8a.m
    mapdh8a.i
    mapdh8a.k
    wph
    cX
    cF
    cY
    cotp
    cI
    cfv
    #
    cG
    cD
    mapdh8b.eg
    wph
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
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdh8a.q
    mapdh8a.i
    mapdh8a.h
    mapdh8a.m
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.j
    mapdh8a.k
    mapdh8d.f
    mapdh8d.mn
    mapdh8d.x
    wph
    cY
    cV
    c.0
    csn
    #
    mapdh8d.y
    eldifad
    #
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wne
    @5
    @0
    csn
    cN
    cfv
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    @0
    mapdh8a.v
    mapdh8a.n
    wph
    cU
    cH
    cK
    cW
    mapdh8a.h
    mapdh8a.u
    mapdh8a.k
    dvhlvec
    wph
    cX
    cV
    @3
    mapdh8d.x
    eldifad
    @4
    wph
    @0
    cV
    @3
    mapdh8d.w
    eldifad
    mapdh8d.xn
    lspindpi
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    wph
    @6
    cM
    cfv
    cG
    csn
    cJ
    cfv
    wceq
    #
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cF
    cG
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    wph
    @2
    cG
    wceq
    @9
    @10
    wa
    mapdh8b.eg
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cG
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdh8a.q
    mapdh8a.i
    mapdh8a.h
    mapdh8a.m
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.j
    mapdh8a.k
    mapdh8d.f
    mapdh8d.mn
    mapdh8d.x
    mapdh8d.y
    @8
    @7
    mapdheq
    mpbid
    simpld
    wph
    vx
    cC
    cD
    cQ
    cR
    @0
    cU
    vh
    cF
    cG
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.q
    mapdh8a.j
    mapdh8a.m
    mapdh8a.i
    mapdh8a.k
    mapdh8d.f
    mapdh8d.mn
    mapdh8b.eg
    mapdh8d.x
    mapdh8d.y
    mapdh8d.vw
    mapdh8d.w
    mapdh8d.xn
    mapdh8a
    mapdh8d.y
    mapdh8d.w
    mapdh8d.wt
    mapdh8d.xt
    mapdh8d.vw
    mapdh8d0.e
    mapdh8d.xn
    mapdh8b
    wph
    vx
    vw
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    @1
    cF
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.q
    mapdh8a.j
    mapdh8a.m
    mapdh8a.i
    mapdh8a.k
    mapdh8d.f
    mapdh8d.mn
    wph
    @1
    eqidd
    mapdh8d.x
    mapdh8d.y
    mapdh8d.xt
    mapdh8d.yz
    mapdh8d.w
    mapdh8d.wt
    mapdh8d.ut
    mapdh8d.vw
    mapdh8d0.e
    mapdh8d.xn
    mapdh8c
    eqtr3d
end
