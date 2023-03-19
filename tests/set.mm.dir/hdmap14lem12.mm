include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "w3a.mm"
include "wrex.mm"
include "clspn.mm"
include "eqid.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "eldifad.mm"
include "hdmap14lem2a.mm"
include "cplusg.mm"
include "simp11.mm"
include "syl.mm"
include "simp13.mm"
include "simp2.mm"
include "simp12.mm"
include "hdmap14lem11.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "wi.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "imp.mm"
include "impbida.mm"

theorem hdmap14lem12
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vg: setvar g
  let vx: setvar x
  assume hdmap14lem12.h: |- H = ( LHyp ` K )
  assume hdmap14lem12.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap14lem12.v: |- V = ( Base ` U )
  assume hdmap14lem12.t: |- .x. = ( .s ` U )
  assume hdmap14lem12.r: |- R = ( Scalar ` U )
  assume hdmap14lem12.b: |- B = ( Base ` R )
  assume hdmap14lem12.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap14lem12.e: |- .xb = ( .s ` C )
  assume hdmap14lem12.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap14lem12.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap14lem12.f: |- ( ph -> F e. B )
  assume hdmap14lem12.p: |- P = ( Scalar ` C )
  assume hdmap14lem12.a: |- A = ( Base ` P )
  assume hdmap14lem12.o: |- .0. = ( 0g ` U )
  assume hdmap14lem12.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap14lem12.g: |- ( ph -> G e. A )

  disjoint A y
  disjoint .xb y
  disjoint F y
  disjoint G y
  disjoint .0. y
  disjoint S y
  disjoint .x. y
  disjoint U y
  disjoint V y
  disjoint X y
  disjoint ph y
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint x y
  disjoint A x
  disjoint B g
  disjoint C g
  disjoint C x
  disjoint .xb g
  disjoint .xb x
  disjoint F g
  disjoint F x
  disjoint G g
  disjoint .0. g
  disjoint P g
  disjoint R g
  disjoint S g
  disjoint S x
  disjoint .x. g
  disjoint .x. x
  disjoint U g
  disjoint U x
  disjoint V g
  disjoint V x
  disjoint X g
  disjoint g ph
  disjoint ph x
  assert |- ( ph -> ( ( S ` ( F .x. X ) ) = ( G .xb ( S ` X ) ) <-> A. y e. ( V \ { .0. } ) ( S ` ( F .x. y ) ) = ( G .xb ( S ` y ) ) ) )

  proof
    wph
    cF
    cX
    c.x
    co
    #
    cS
    cfv
    #
    cG
    cX
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    cF
    vy
    cv
    #
    c.x
    co
    #
    cS
    cfv
    #
    cG
    @5
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    vy
    cV
    c.0
    csn
    #
    cdif
    #
    wral
    #
    wph
    @4
    wa
    @10
    vy
    @12
    wph
    @4
    @5
    @12
    wcel
    #
    @10
    wph
    @4
    @14
    w3a
    #
    @7
    vg
    cv
    #
    @8
    c.xb
    co
    #
    wceq
    #
    vg
    cA
    wrex
    @10
    @15
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
    @5
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.v
    hdmap14lem12.t
    hdmap14lem12.r
    hdmap14lem12.b
    hdmap14lem12.c
    hdmap14lem12.e
    @19
    eqid
    hdmap14lem12.p
    hdmap14lem12.a
    hdmap14lem12.s
    wph
    @4
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @14
    hdmap14lem12.k
    3ad2ant1
    @15
    @5
    cV
    @11
    wph
    @4
    @14
    simp3
    eldifad
    wph
    @4
    cF
    cB
    wcel
    #
    @14
    hdmap14lem12.f
    3ad2ant1
    hdmap14lem2a
    @15
    @18
    @10
    vg
    cA
    @15
    @16
    cA
    wcel
    #
    @18
    w3a
    #
    @7
    @17
    @9
    @15
    @22
    @18
    simp3
    #
    @23
    cG
    @16
    @8
    c.xb
    @23
    cA
    cB
    cC
    cP
    cU
    cplusg
    cfv
    #
    cC
    cplusg
    cfv
    #
    cR
    cS
    c.xb
    c.x
    cU
    cF
    cG
    cH
    @16
    cK
    cU
    clspn
    cfv
    #
    cV
    cW
    cX
    @5
    c.0
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.v
    @25
    eqid
    hdmap14lem12.t
    hdmap14lem12.o
    @27
    eqid
    hdmap14lem12.r
    hdmap14lem12.b
    hdmap14lem12.c
    @26
    eqid
    hdmap14lem12.e
    hdmap14lem12.p
    hdmap14lem12.a
    hdmap14lem12.s
    @23
    wph
    @20
    wph
    @4
    @14
    @22
    @18
    simp11
    #
    hdmap14lem12.k
    syl
    @23
    wph
    cX
    @12
    wcel
    #
    @28
    hdmap14lem12.x
    syl
    wph
    @4
    @14
    @22
    @18
    simp13
    @23
    wph
    @21
    @28
    hdmap14lem12.f
    syl
    @23
    wph
    cG
    cA
    wcel
    @28
    hdmap14lem12.g
    syl
    @15
    @22
    @18
    simp2
    wph
    @4
    @14
    @22
    @18
    simp12
    @24
    hdmap14lem11
    oveq1d
    eqtr4d
    rexlimdv3a
    mpd
    3expia
    ralrimiv
    wph
    @13
    @4
    wph
    @29
    @13
    @4
    wi
    hdmap14lem12.x
    @10
    @4
    vy
    cX
    @12
    @5
    cX
    wceq
    #
    @7
    @1
    @9
    @3
    @30
    @6
    @0
    cS
    @5
    cX
    cF
    c.x
    oveq2
    fveq2d
    @30
    @8
    @2
    cG
    c.xb
    @5
    cX
    cS
    fveq2
    oveq2d
    eqeq12d
    rspcv
    syl
    imp
    impbida
end
