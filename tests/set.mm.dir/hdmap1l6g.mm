include "cv.mm"
include "co.mm"
include "cotp.mm"
include "cfv.mm"
include "hdmap1l6d.mm"
include "hdmap1l6e.mm"
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
include "hdmap1l6f.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"

theorem hdmap1l6g
  let wph: wff ph
  let vw: setvar w
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume hdmap1l6.h: |- H = ( LHyp ` K )
  assume hdmap1l6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1l6.v: |- V = ( Base ` U )
  assume hdmap1l6.p: |- .+ = ( +g ` U )
  assume hdmap1l6.s: |- .- = ( -g ` U )
  assume hdmap1l6c.o: |- .0. = ( 0g ` U )
  assume hdmap1l6.n: |- N = ( LSpan ` U )
  assume hdmap1l6.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1l6.d: |- D = ( Base ` C )
  assume hdmap1l6.a: |- .+b = ( +g ` C )
  assume hdmap1l6.r: |- R = ( -g ` C )
  assume hdmap1l6.q: |- Q = ( 0g ` C )
  assume hdmap1l6.l: |- L = ( LSpan ` C )
  assume hdmap1l6.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1l6.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1l6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1l6.f: |- ( ph -> F e. D )
  assume hdmap1l6cl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1l6.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )
  assume hdmap1l6d.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume hdmap1l6d.yz: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )
  assume hdmap1l6d.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap1l6d.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume hdmap1l6d.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume hdmap1l6d.wn: |- ( ph -> -. w e. ( N ` { X , Y } ) )


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
    vw
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.r
    hdmap1l6.q
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6cl.x
    hdmap1l6.mn
    hdmap1l6d.xn
    hdmap1l6d.yz
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.wn
    hdmap1l6d
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
    vw
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.r
    hdmap1l6.q
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6cl.x
    hdmap1l6.mn
    hdmap1l6d.xn
    hdmap1l6d.yz
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.wn
    hdmap1l6e
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
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlmod
    wph
    @0
    cV
    c.0
    csn
    #
    hdmap1l6d.w
    eldifad
    wph
    cY
    cV
    @13
    hdmap1l6d.y
    eldifad
    wph
    cZ
    cV
    @13
    hdmap1l6d.z
    eldifad
    c.pl
    cV
    cU
    @0
    cY
    cZ
    hdmap1l6.v
    hdmap1l6.p
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
    vw
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.r
    hdmap1l6.q
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6cl.x
    hdmap1l6.mn
    hdmap1l6d.xn
    hdmap1l6d.yz
    hdmap1l6d.y
    hdmap1l6d.z
    hdmap1l6d.w
    hdmap1l6d.wn
    hdmap1l6f
    oveq1d
    3eqtr3d
    eqtr3d
end
