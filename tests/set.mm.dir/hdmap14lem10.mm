include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "clspn.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "csn.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "hdmap14lem2a.mm"
include "w3a.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "wne.mm"
include "simp2.mm"
include "simp3.mm"
include "hdmap14lem9.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hdmap14lem10
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vg: setvar g
  assume hdmap14lem8.h: |- H = ( LHyp ` K )
  assume hdmap14lem8.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap14lem8.v: |- V = ( Base ` U )
  assume hdmap14lem8.q: |- .+ = ( +g ` U )
  assume hdmap14lem8.t: |- .x. = ( .s ` U )
  assume hdmap14lem8.o: |- .0. = ( 0g ` U )
  assume hdmap14lem8.n: |- N = ( LSpan ` U )
  assume hdmap14lem8.r: |- R = ( Scalar ` U )
  assume hdmap14lem8.b: |- B = ( Base ` R )
  assume hdmap14lem8.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap14lem8.d: |- .+b = ( +g ` C )
  assume hdmap14lem8.e: |- .xb = ( .s ` C )
  assume hdmap14lem8.p: |- P = ( Scalar ` C )
  assume hdmap14lem8.a: |- A = ( Base ` P )
  assume hdmap14lem8.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap14lem8.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap14lem8.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap14lem8.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap14lem8.f: |- ( ph -> F e. B )
  assume hdmap14lem8.g: |- ( ph -> G e. A )
  assume hdmap14lem8.i: |- ( ph -> I e. A )
  assume hdmap14lem8.xx: |- ( ph -> ( S ` ( F .x. X ) ) = ( G .xb ( S ` X ) ) )
  assume hdmap14lem8.yy: |- ( ph -> ( S ` ( F .x. Y ) ) = ( I .xb ( S ` Y ) ) )
  assume hdmap14lem8.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> G = I )

  proof
    wph
    cF
    cX
    cY
    c.pl
    co
    #
    c.x
    co
    cS
    cfv
    vg
    cv
    #
    @0
    cS
    cfv
    c.xb
    co
    wceq
    #
    vg
    cA
    wrex
    cG
    cI
    wceq
    #
    wph
    cA
    cB
    cC
    cP
    cR
    cS
    c.xb
    c.x
    cU
    vg
    cF
    cH
    cK
    cC
    clspn
    cfv
    #
    cV
    cW
    @0
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.t
    hdmap14lem8.r
    hdmap14lem8.b
    hdmap14lem8.c
    hdmap14lem8.e
    @4
    eqid
    hdmap14lem8.p
    hdmap14lem8.a
    hdmap14lem8.s
    hdmap14lem8.k
    wph
    cU
    clmod
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    @0
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.k
    dvhlmod
    wph
    cX
    cV
    c.0
    csn
    #
    hdmap14lem8.x
    eldifad
    wph
    cY
    cV
    @5
    hdmap14lem8.y
    eldifad
    c.pl
    cV
    cU
    cX
    cY
    hdmap14lem8.v
    hdmap14lem8.q
    lmodvacl
    syl3anc
    hdmap14lem8.f
    hdmap14lem2a
    wph
    @2
    @3
    vg
    cA
    wph
    @1
    cA
    wcel
    #
    @2
    w3a
    cA
    cB
    cC
    cP
    c.pl
    c.pb
    cR
    cS
    c.xb
    c.x
    cU
    cF
    cG
    cH
    cI
    @1
    cK
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.q
    hdmap14lem8.t
    hdmap14lem8.o
    hdmap14lem8.n
    hdmap14lem8.r
    hdmap14lem8.b
    hdmap14lem8.c
    hdmap14lem8.d
    hdmap14lem8.e
    hdmap14lem8.p
    hdmap14lem8.a
    hdmap14lem8.s
    wph
    @6
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    hdmap14lem8.k
    3ad2ant1
    wph
    @6
    cX
    cV
    @5
    cdif
    #
    wcel
    @2
    hdmap14lem8.x
    3ad2ant1
    wph
    @6
    cY
    @7
    wcel
    @2
    hdmap14lem8.y
    3ad2ant1
    wph
    @6
    cF
    cB
    wcel
    @2
    hdmap14lem8.f
    3ad2ant1
    wph
    @6
    cG
    cA
    wcel
    @2
    hdmap14lem8.g
    3ad2ant1
    wph
    @6
    cI
    cA
    wcel
    @2
    hdmap14lem8.i
    3ad2ant1
    wph
    @6
    cF
    cX
    c.x
    co
    cS
    cfv
    cG
    cX
    cS
    cfv
    c.xb
    co
    wceq
    @2
    hdmap14lem8.xx
    3ad2ant1
    wph
    @6
    cF
    cY
    c.x
    co
    cS
    cfv
    cI
    cY
    cS
    cfv
    c.xb
    co
    wceq
    @2
    hdmap14lem8.yy
    3ad2ant1
    wph
    @6
    cX
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    wne
    @2
    hdmap14lem8.ne
    3ad2ant1
    wph
    @6
    @2
    simp2
    wph
    @6
    @2
    simp3
    hdmap14lem9
    rexlimdv3a
    mpd
end
