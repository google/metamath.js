include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "dvhlvec.mm"
include "eldifad.mm"
include "lspindpi.mm"
include "simprd.mm"
include "lspexch.mm"
include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "clvec.mm"
include "adantr.mm"
include "cdif.mm"
include "simpr.mm"
include "mtand.mm"
include "mapdh8b.mm"

theorem mapdh8c
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
  let cE: class E
  let cF: class F
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
  let cG: class G
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
  assume mapdh8c.f: |- ( ph -> F e. D )
  assume mapdh8c.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8c.a: |- ( ph -> ( I ` <. X , F , w >. ) = E )
  assume mapdh8c.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8c.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8c.xt: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8c.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { T } ) )
  assume mapdh8c.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh8c.wt: |- ( ph -> ( N ` { w } ) =/= ( N ` { T } ) )
  assume mapdh8c.ut: |- ( ph -> ( N ` { X } ) =/= ( N ` { T } ) )
  assume mapdh8c.vw: |- ( ph -> ( N ` { Y } ) =/= ( N ` { w } ) )
  assume mapdh8c.e: |- ( ph -> X e. ( N ` { Y , T } ) )
  assume mapdh8c.xn: |- ( ph -> -. X e. ( N ` { Y , w } ) )

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
  disjoint h w
  disjoint w x
  disjoint G h
  disjoint G x
  disjoint Z h
  disjoint Z x
  assert |- ( ph -> ( I ` <. w , E , T >. ) = ( I ` <. X , F , T >. ) )

  proof
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
    cE
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
    cY
    cX
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
    mapdh8c.f
    mapdh8c.mn
    mapdh8c.a
    mapdh8c.x
    mapdh8c.w
    mapdh8c.wt
    mapdh8c.xt
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
    @0
    vw
    cv
    #
    csn
    cN
    cfv
    #
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    @2
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
    #
    wph
    cX
    cV
    c.0
    csn
    #
    mapdh8c.x
    eldifad
    #
    wph
    cY
    cV
    @5
    mapdh8c.y
    eldifad
    #
    wph
    @2
    cV
    @5
    mapdh8c.w
    eldifad
    #
    mapdh8c.xn
    lspindpi
    simprd
    wph
    cN
    cV
    cU
    cX
    cY
    c.0
    cT
    mapdh8a.v
    mapdh8a.o
    mapdh8a.n
    @4
    mapdh8c.x
    @7
    wph
    cT
    cV
    @5
    mapdh8c.xt
    eldifad
    mapdh8c.ut
    mapdh8c.e
    lspexch
    wph
    cY
    cX
    @2
    cpr
    cN
    cfv
    wcel
    #
    cX
    cY
    @2
    cpr
    cN
    cfv
    wcel
    mapdh8c.xn
    wph
    @9
    wa
    cN
    cV
    cU
    cY
    cX
    c.0
    @2
    mapdh8a.v
    mapdh8a.o
    mapdh8a.n
    wph
    cU
    clvec
    wcel
    @9
    @4
    adantr
    wph
    cY
    cV
    @5
    cdif
    wcel
    @9
    mapdh8c.y
    adantr
    wph
    cX
    cV
    wcel
    @9
    @6
    adantr
    wph
    @2
    cV
    wcel
    @9
    @8
    adantr
    wph
    @1
    @3
    wne
    @9
    mapdh8c.vw
    adantr
    wph
    @9
    simpr
    lspexch
    mtand
    mapdh8b
end
