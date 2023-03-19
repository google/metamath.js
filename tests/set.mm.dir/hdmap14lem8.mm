include "cfv.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "csn.mm"
include "eldifad.mm"
include "hdmapcl.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "hdmapadd.mm"
include "oveq2d.mm"
include "dvhlmod.mm"
include "fveq2d.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "eqtr3d.mm"

theorem hdmap14lem8
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
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
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
  assume hdmap14lem8.j: |- ( ph -> J e. A )
  assume hdmap14lem8.xy: |- ( ph -> ( S ` ( F .x. ( X .+ Y ) ) ) = ( J .xb ( S ` ( X .+ Y ) ) ) )


  assert |- ( ph -> ( ( J .xb ( S ` X ) ) .+b ( J .xb ( S ` Y ) ) ) = ( ( G .xb ( S ` X ) ) .+b ( I .xb ( S ` Y ) ) ) )

  proof
    wph
    cJ
    cX
    cS
    cfv
    #
    cY
    cS
    cfv
    #
    c.pb
    co
    #
    c.xb
    co
    #
    cJ
    @0
    c.xb
    co
    cJ
    @1
    c.xb
    co
    c.pb
    co
    #
    cG
    @0
    c.xb
    co
    #
    cI
    @1
    c.xb
    co
    #
    c.pb
    co
    #
    wph
    cC
    clmod
    wcel
    cJ
    cA
    wcel
    @0
    cC
    cbs
    cfv
    #
    wcel
    @1
    @8
    wcel
    @3
    @4
    wceq
    wph
    cC
    cH
    cK
    cW
    hdmap14lem8.h
    hdmap14lem8.c
    hdmap14lem8.k
    lcdlmod
    hdmap14lem8.j
    wph
    cC
    @8
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.c
    @8
    eqid
    #
    hdmap14lem8.s
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
    hdmapcl
    wph
    cC
    @8
    cS
    cY
    cU
    cH
    cK
    cV
    cW
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.c
    @9
    hdmap14lem8.s
    hdmap14lem8.k
    wph
    cY
    cV
    @10
    hdmap14lem8.y
    eldifad
    #
    hdmapcl
    c.pb
    cJ
    c.xb
    cP
    cA
    @8
    cC
    @0
    @1
    @9
    hdmap14lem8.d
    hdmap14lem8.p
    hdmap14lem8.e
    hdmap14lem8.a
    lmodvsdi
    syl13anc
    wph
    cJ
    cX
    cY
    c.pl
    co
    #
    cS
    cfv
    #
    c.xb
    co
    #
    @3
    @7
    wph
    @14
    @2
    cJ
    c.xb
    wph
    cC
    c.pl
    c.pb
    cS
    cU
    cH
    cK
    cV
    cW
    cX
    cY
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.q
    hdmap14lem8.c
    hdmap14lem8.d
    hdmap14lem8.s
    hdmap14lem8.k
    @11
    @12
    hdmapadd
    oveq2d
    wph
    cF
    @13
    c.x
    co
    #
    cS
    cfv
    #
    @15
    @7
    hdmap14lem8.xy
    wph
    @17
    cF
    cX
    c.x
    co
    #
    cF
    cY
    c.x
    co
    #
    c.pl
    co
    #
    cS
    cfv
    @18
    cS
    cfv
    #
    @19
    cS
    cfv
    #
    c.pb
    co
    @7
    wph
    @16
    @20
    cS
    wph
    cU
    clmod
    wcel
    #
    cF
    cB
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @16
    @20
    wceq
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
    hdmap14lem8.f
    @11
    @12
    c.pl
    cF
    c.x
    cR
    cB
    cV
    cU
    cX
    cY
    hdmap14lem8.v
    hdmap14lem8.q
    hdmap14lem8.r
    hdmap14lem8.t
    hdmap14lem8.b
    lmodvsdi
    syl13anc
    fveq2d
    wph
    cC
    c.pl
    c.pb
    cS
    cU
    cH
    cK
    cV
    cW
    @18
    @19
    hdmap14lem8.h
    hdmap14lem8.u
    hdmap14lem8.v
    hdmap14lem8.q
    hdmap14lem8.c
    hdmap14lem8.d
    hdmap14lem8.s
    hdmap14lem8.k
    wph
    @23
    @24
    @25
    @18
    cV
    wcel
    @27
    hdmap14lem8.f
    @11
    cF
    c.x
    cR
    cB
    cV
    cU
    cX
    hdmap14lem8.v
    hdmap14lem8.r
    hdmap14lem8.t
    hdmap14lem8.b
    lmodvscl
    syl3anc
    wph
    @23
    @24
    @26
    @19
    cV
    wcel
    @27
    hdmap14lem8.f
    @12
    cF
    c.x
    cR
    cB
    cV
    cU
    cY
    hdmap14lem8.v
    hdmap14lem8.r
    hdmap14lem8.t
    hdmap14lem8.b
    lmodvscl
    syl3anc
    hdmapadd
    wph
    @21
    @5
    @22
    @6
    c.pb
    hdmap14lem8.xx
    hdmap14lem8.yy
    oveq12d
    3eqtrd
    eqtr3d
    eqtr3d
    eqtr3d
end
