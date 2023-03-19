include "cotp.mm"
include "cfv.mm"
include "cv.mm"
include "mapdh8ab.mm"
include "eqtrd.mm"

theorem mapdh8ac
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
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
  assume mapdh8ac.f: |- ( ph -> F e. D )
  assume mapdh8ac.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8ac.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8ac.ee: |- ( ph -> ( I ` <. X , F , Z >. ) = E )
  assume mapdh8ac.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8ac.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8ac.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh8ac.t: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8ac.yn: |- ( ph -> ( N ` { X } ) = ( N ` { T } ) )
  assume mapdh8ac.ew: |- ( ph -> ( I ` <. X , F , w >. ) = B )
  assume mapdh8ac.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh8ac.yw: |- ( ph -> ( N ` { Y } ) =/= ( N ` { w } ) )
  assume mapdh8ac.xy: |- ( ph -> -. X e. ( N ` { Y , w } ) )
  assume mapdh8ac.wz: |- ( ph -> ( N ` { w } ) =/= ( N ` { Z } ) )
  assume mapdh8ac.xz: |- ( ph -> -. X e. ( N ` { w , Z } ) )

  disjoint h x
  disjoint B h
  disjoint B x
  disjoint h w
  disjoint w x
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
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. Z , E , T >. ) )

  proof
    wph
    cY
    cG
    cT
    cotp
    cI
    cfv
    vw
    cv
    #
    cB
    cT
    cotp
    cI
    cfv
    cZ
    cE
    cT
    cotp
    cI
    cfv
    wph
    vx
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    cB
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
    @0
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
    mapdh8ac.f
    mapdh8ac.mn
    mapdh8ac.eg
    mapdh8ac.ew
    mapdh8ac.x
    mapdh8ac.y
    mapdh8ac.w
    mapdh8ac.t
    mapdh8ac.yw
    mapdh8ac.xy
    mapdh8ac.yn
    mapdh8ab
    wph
    vx
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    cE
    cF
    cB
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
    @0
    c.0
    cZ
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
    mapdh8ac.f
    mapdh8ac.mn
    mapdh8ac.ew
    mapdh8ac.ee
    mapdh8ac.x
    mapdh8ac.w
    mapdh8ac.z
    mapdh8ac.t
    mapdh8ac.wz
    mapdh8ac.xz
    mapdh8ac.yn
    mapdh8ab
    eqtrd
end
