include "cotp.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "wne.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "dvhlvec.mm"
include "eldifad.mm"
include "lspindpi.mm"
include "simpld.mm"
include "lspindp1.mm"
include "simprd.mm"
include "eqidd.mm"
include "mapdh6aN.mm"

theorem mapdh6fN
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
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
  let cZ: class Z
  let cG: class G
  let cE: class E
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh.h: |- H = ( LHyp ` K )
  assume mapdh.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh.v: |- V = ( Base ` U )
  assume mapdh.s: |- .- = ( -g ` U )
  assume mapdhc.o: |- .0. = ( 0g ` U )
  assume mapdh.n: |- N = ( LSpan ` U )
  assume mapdh.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh.d: |- D = ( Base ` C )
  assume mapdh.r: |- R = ( -g ` C )
  assume mapdh.j: |- J = ( LSpan ` C )
  assume mapdh.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdhc.f: |- ( ph -> F e. D )
  assume mapdh.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdhcl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh.p: |- .+ = ( +g ` U )
  assume mapdh.a: |- .+b = ( +g ` C )
  assume mapdh6d.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh6d.yz: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )
  assume mapdh6d.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh6d.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh6d.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh6d.wn: |- ( ph -> -. w e. ( N ` { X , Y } ) )

  disjoint D x
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint J x
  disjoint M x
  disjoint N x
  disjoint .0. x
  disjoint Q x
  disjoint R x
  disjoint .- x
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint h ph
  disjoint .0. h
  disjoint C h
  disjoint D h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint R h
  disjoint U h
  disjoint .- h
  disjoint h w
  disjoint Z h
  disjoint Z x
  disjoint .+b h
  disjoint I h
  disjoint I x
  disjoint .+ h
  disjoint .+ x
  disjoint w x
  disjoint G h
  disjoint G x
  disjoint E h
  assert |- ( ph -> ( I ` <. X , F , ( w .+ Y ) >. ) = ( ( I ` <. X , F , w >. ) .+b ( I ` <. X , F , Y >. ) ) )

  proof
    wph
    vx
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    vh
    cX
    cF
    cY
    cotp
    cI
    cfv
    #
    cF
    cX
    cF
    vw
    cv
    #
    cotp
    cI
    cfv
    #
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
    @1
    c.0
    cY
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    mapdh.p
    mapdh.a
    mapdh6d.w
    mapdh6d.y
    wph
    @1
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
    #
    cX
    @1
    cY
    cpr
    cN
    cfv
    wcel
    wn
    wph
    cN
    cV
    cU
    cX
    cY
    c.0
    @1
    mapdh.v
    mapdhc.o
    mapdh.n
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlvec
    #
    mapdhcl.x
    wph
    cY
    cV
    c.0
    csn
    #
    mapdh6d.y
    eldifad
    #
    wph
    @1
    cV
    @7
    mapdh6d.w
    eldifad
    #
    wph
    cX
    csn
    cN
    cfv
    #
    @4
    wne
    @10
    cZ
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
    cZ
    mapdh.v
    mapdh.n
    @6
    wph
    cX
    cV
    @7
    mapdhcl.x
    eldifad
    #
    @8
    wph
    cZ
    cV
    @7
    mapdh6d.z
    eldifad
    mapdh6d.xn
    lspindpi
    simpld
    mapdh6d.wn
    lspindp1
    simprd
    wph
    @3
    @10
    wne
    @5
    wph
    cN
    cV
    cU
    @1
    cX
    cY
    mapdh.v
    mapdh.n
    @6
    @9
    @11
    @8
    mapdh6d.wn
    lspindpi
    simprd
    wph
    @2
    eqidd
    wph
    @0
    eqidd
    mapdh6aN
end
