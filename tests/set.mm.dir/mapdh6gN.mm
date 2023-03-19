include "cv.mm"
include "co.mm"
include "cotp.mm"
include "cfv.mm"
include "mapdh6dN.mm"
include "mapdh6eN.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "dvhlmod.mm"
include "csn.mm"
include "eldifad.mm"
include "lmodass.mm"
include "syl13anc.mm"
include "oteq3d.mm"
include "fveq2d.mm"
include "mapdh6fN.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"

theorem mapdh6gN
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
  assert |- ( ph -> ( ( I ` <. X , F , w >. ) .+b ( I ` <. X , F , ( Y .+ Z ) >. ) ) = ( ( ( I ` <. X , F , w >. ) .+b ( I ` <. X , F , Y >. ) ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cX
    cF
    vw
    cv
    #
    cY
    cZ
    c.pl
    co
    #
    c.pl
    co
    #
    cotp
    #
    cI
    cfv
    #
    cX
    cF
    @0
    cotp
    cI
    cfv
    #
    cX
    cF
    @1
    cotp
    cI
    cfv
    c.pb
    co
    @5
    cX
    cF
    cY
    cotp
    cI
    cfv
    c.pb
    co
    #
    cX
    cF
    cZ
    cotp
    cI
    cfv
    #
    c.pb
    co
    #
    wph
    vx
    vw
    cC
    cD
    c.pl
    c.pb
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
    cZ
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
    mapdh6d.xn
    mapdh6d.yz
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.wn
    mapdh6dN
    wph
    cX
    cF
    @0
    cY
    c.pl
    co
    #
    cZ
    c.pl
    co
    #
    cotp
    #
    cI
    cfv
    cX
    cF
    @9
    cotp
    cI
    cfv
    #
    @7
    c.pb
    co
    @4
    @8
    wph
    vx
    vw
    cC
    cD
    c.pl
    c.pb
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
    cZ
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
    mapdh6d.xn
    mapdh6d.yz
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.wn
    mapdh6eN
    wph
    @11
    @3
    cI
    wph
    @10
    @2
    cX
    cF
    wph
    cU
    clmod
    wcel
    @0
    cV
    wcel
    cY
    cV
    wcel
    cZ
    cV
    wcel
    @10
    @2
    wceq
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlmod
    wph
    @0
    cV
    c.0
    csn
    #
    mapdh6d.w
    eldifad
    wph
    cY
    cV
    @13
    mapdh6d.y
    eldifad
    wph
    cZ
    cV
    @13
    mapdh6d.z
    eldifad
    c.pl
    cV
    cU
    @0
    cY
    cZ
    mapdh.v
    mapdh.p
    lmodass
    syl13anc
    oteq3d
    fveq2d
    wph
    @12
    @6
    @7
    c.pb
    wph
    vx
    vw
    cC
    cD
    c.pl
    c.pb
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
    cZ
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
    mapdh6d.xn
    mapdh6d.yz
    mapdh6d.y
    mapdh6d.z
    mapdh6d.w
    mapdh6d.wn
    mapdh6fN
    oveq1d
    3eqtr3d
    eqtr3d
end
