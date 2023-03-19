include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "wceq.mm"
include "csn.mm"
include "eldifad.mm"
include "dvh3dim.mm"
include "w3a.mm"
include "co.mm"
include "clspn.mm"
include "eqid.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "hdmap14lem2a.mm"
include "simp11.mm"
include "syl.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "simp12.mm"
include "simp13.mm"
include "lssneln0.mm"
include "cdif.mm"
include "simp3.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "hdmap14lem10.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hdmap14lem11
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
  let vz: setvar z
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


  assert |- ( ph -> G = I )

  proof
    wph
    vz
    cv
    #
    cX
    cY
    cpr
    cN
    cfv
    #
    wcel
    wn
    #
    vz
    cV
    wrex
    cG
    cI
    wceq
    #
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cY
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.n
    hdmap14lem8.k
    wph
    cX
    cV
    c.0
    csn
    #
    hdmap14lem8.x
    eldifad
    #
    wph
    cY
    cV
    @4
    hdmap14lem8.y
    eldifad
    #
    dvh3dim
    wph
    @2
    @3
    vz
    cV
    wph
    @0
    cV
    wcel
    #
    @2
    w3a
    #
    cF
    @0
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
    @3
    @8
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
    @11
    eqid
    hdmap14lem8.p
    hdmap14lem8.a
    hdmap14lem8.s
    wph
    @7
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    hdmap14lem8.k
    3ad2ant1
    wph
    @7
    @2
    simp2
    wph
    @7
    cF
    cB
    wcel
    #
    @2
    hdmap14lem8.f
    3ad2ant1
    hdmap14lem2a
    @8
    @10
    @3
    vg
    cA
    @8
    @9
    cA
    wcel
    #
    @10
    w3a
    #
    @9
    cG
    cI
    @15
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
    @9
    cH
    cG
    cK
    cN
    cV
    cW
    @0
    cX
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
    @15
    wph
    @12
    wph
    @7
    @2
    @14
    @10
    simp11
    #
    hdmap14lem8.k
    syl
    #
    @15
    cU
    clss
    cfv
    #
    @1
    cV
    cU
    @0
    c.0
    hdmap14lem8.v
    hdmap14lem8.o
    @18
    eqid
    #
    @15
    wph
    cU
    clmod
    wcel
    @16
    wph
    cU
    cH
    cK
    cW
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.k
    dvhlmod
    #
    syl
    @15
    wph
    @1
    @18
    wcel
    @16
    wph
    @18
    cN
    cV
    cU
    cX
    cY
    hdmap14lem8.v
    @19
    hdmap14lem8.n
    @20
    @5
    @6
    lspprcl
    syl
    wph
    @7
    @2
    @14
    @10
    simp12
    #
    wph
    @7
    @2
    @14
    @10
    simp13
    #
    lssneln0
    #
    @15
    wph
    cX
    cV
    @4
    cdif
    #
    wcel
    @16
    hdmap14lem8.x
    syl
    @15
    wph
    @13
    @16
    hdmap14lem8.f
    syl
    #
    @8
    @14
    @10
    simp2
    #
    @15
    wph
    cG
    cA
    wcel
    @16
    hdmap14lem8.g
    syl
    @8
    @14
    @10
    simp3
    #
    @15
    wph
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
    @16
    hdmap14lem8.xx
    syl
    @15
    @0
    csn
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    wne
    #
    @28
    cY
    csn
    cN
    cfv
    wne
    #
    @15
    cN
    cV
    cU
    @0
    cX
    cY
    hdmap14lem8.v
    hdmap14lem8.n
    @15
    wph
    cU
    clvec
    wcel
    @16
    wph
    cU
    cH
    cK
    cW
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.k
    dvhlvec
    syl
    @21
    @15
    wph
    cX
    cV
    wcel
    @16
    @5
    syl
    @15
    wph
    cY
    cV
    wcel
    @16
    @6
    syl
    @22
    lspindpi
    #
    simpld
    hdmap14lem10
    @15
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
    @9
    cH
    cI
    cK
    cN
    cV
    cW
    @0
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
    @17
    @23
    @15
    wph
    cY
    @24
    wcel
    @16
    hdmap14lem8.y
    syl
    @25
    @26
    @15
    wph
    cI
    cA
    wcel
    @16
    hdmap14lem8.i
    syl
    @27
    @15
    wph
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
    @16
    hdmap14lem8.yy
    syl
    @15
    @29
    @30
    @31
    simprd
    hdmap14lem10
    eqtr3d
    rexlimdv3a
    mpd
    rexlimdv3a
    mpd
end
