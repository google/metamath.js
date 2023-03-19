include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cun.mm"
include "hdmap14lem12.mm"
include "wa.mm"
include "wcel.mm"
include "velsn.mm"
include "c0g.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "lmodvs0.mm"
include "syl2anc.mm"
include "hdmapval0.mm"
include "oveq2d.mm"
include "dvhlmod.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "oveq2.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "biantrud.mm"
include "ralunb.mm"
include "syl6bbr.mm"
include "lmod0vcl.mm"
include "difsnid.mm"
include "3syl.mm"
include "raleqdv.mm"
include "3bitrd.mm"

theorem hdmap14lem13
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
  assert |- ( ph -> ( ( S ` ( F .x. X ) ) = ( G .xb ( S ` X ) ) <-> A. y e. V ( S ` ( F .x. y ) ) = ( G .xb ( S ` y ) ) ) )

  proof
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
    @0
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
    @5
    vy
    @7
    @6
    cun
    #
    wral
    #
    @5
    vy
    cV
    wral
    wph
    vy
    cA
    cB
    cC
    cP
    cR
    cS
    c.xb
    c.x
    cU
    cF
    cG
    cH
    cK
    cV
    cW
    cX
    c.0
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.v
    hdmap14lem12.t
    hdmap14lem12.r
    hdmap14lem12.b
    hdmap14lem12.c
    hdmap14lem12.e
    hdmap14lem12.s
    hdmap14lem12.k
    hdmap14lem12.f
    hdmap14lem12.p
    hdmap14lem12.a
    hdmap14lem12.o
    hdmap14lem12.x
    hdmap14lem12.g
    hdmap14lem12
    wph
    @8
    @8
    @5
    vy
    @6
    wral
    #
    wa
    @10
    wph
    @11
    @8
    wph
    @5
    vy
    @6
    @0
    @6
    wcel
    @0
    c.0
    wceq
    #
    wph
    @5
    vy
    c.0
    velsn
    wph
    @5
    @12
    cF
    c.0
    c.x
    co
    #
    cS
    cfv
    #
    cG
    c.0
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    wph
    cG
    cC
    c0g
    cfv
    #
    c.xb
    co
    #
    @17
    @16
    @14
    wph
    cC
    clmod
    wcel
    cG
    cA
    wcel
    @18
    @17
    wceq
    wph
    cC
    cH
    cK
    cW
    hdmap14lem12.h
    hdmap14lem12.c
    hdmap14lem12.k
    lcdlmod
    hdmap14lem12.g
    c.xb
    cP
    cA
    cC
    cG
    @17
    hdmap14lem12.p
    hdmap14lem12.e
    hdmap14lem12.a
    @17
    eqid
    #
    lmodvs0
    syl2anc
    wph
    @15
    @17
    cG
    c.xb
    wph
    cC
    @17
    cS
    cU
    cH
    cK
    cW
    c.0
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.o
    hdmap14lem12.c
    @19
    hdmap14lem12.s
    hdmap14lem12.k
    hdmapval0
    #
    oveq2d
    wph
    @14
    @15
    @17
    wph
    @13
    c.0
    cS
    wph
    cU
    clmod
    wcel
    #
    cF
    cB
    wcel
    @13
    c.0
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.k
    dvhlmod
    #
    hdmap14lem12.f
    c.x
    cR
    cB
    cU
    cF
    c.0
    hdmap14lem12.r
    hdmap14lem12.t
    hdmap14lem12.b
    hdmap14lem12.o
    lmodvs0
    syl2anc
    fveq2d
    @20
    eqtrd
    3eqtr4rd
    @12
    @2
    @14
    @4
    @16
    @12
    @1
    @13
    cS
    @0
    c.0
    cF
    c.x
    oveq2
    fveq2d
    @12
    @3
    @15
    cG
    c.xb
    @0
    c.0
    cS
    fveq2
    oveq2d
    eqeq12d
    syl5ibrcom
    syl5bi
    ralrimiv
    biantrud
    @5
    vy
    @7
    @6
    ralunb
    syl6bbr
    wph
    @5
    vy
    @9
    cV
    wph
    @21
    c.0
    cV
    wcel
    @9
    cV
    wceq
    @22
    cV
    cU
    c.0
    hdmap14lem12.v
    hdmap14lem12.o
    lmod0vcl
    cV
    c.0
    difsnid
    3syl
    raleqdv
    3bitrd
end
