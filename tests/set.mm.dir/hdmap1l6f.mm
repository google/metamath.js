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
include "hdmap1l6a.mm"

theorem hdmap1l6f
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


  assert |- ( ph -> ( I ` <. X , F , ( w .+ Y ) >. ) = ( ( I ` <. X , F , w >. ) .+b ( I ` <. X , F , Y >. ) ) )

  proof
    wph
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
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
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    @1
    c.0
    cY
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
    hdmap1l6d.w
    hdmap1l6d.y
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
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    wph
    cU
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlvec
    #
    hdmap1l6cl.x
    wph
    cY
    cV
    c.0
    csn
    #
    hdmap1l6d.y
    eldifad
    #
    wph
    @1
    cV
    @7
    hdmap1l6d.w
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
    hdmap1l6.v
    hdmap1l6.n
    @6
    wph
    cX
    cV
    @7
    hdmap1l6cl.x
    eldifad
    #
    @8
    wph
    cZ
    cV
    @7
    hdmap1l6d.z
    eldifad
    hdmap1l6d.xn
    lspindpi
    simpld
    hdmap1l6d.wn
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
    hdmap1l6.v
    hdmap1l6.n
    @6
    @9
    @11
    @8
    hdmap1l6d.wn
    lspindpi
    simprd
    wph
    @2
    eqidd
    wph
    @0
    eqidd
    hdmap1l6a
end
