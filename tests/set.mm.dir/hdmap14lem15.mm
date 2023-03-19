include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "wreu.mm"
include "eqid.mm"
include "hdmap14lem14.mm"
include "wb.mm"
include "lcdsbase.mm"
include "reueq1.mm"
include "syl.mm"
include "mpbid.mm"

theorem hdmap14lem15
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vy: setvar y
  let cA: class A
  let cG: class G
  let c.0: class .0.
  let cP: class P
  let cX: class X
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

  disjoint g x
  disjoint B g
  disjoint C g
  disjoint C x
  disjoint .xb g
  disjoint .xb x
  disjoint F g
  disjoint F x
  disjoint R g
  disjoint S g
  disjoint S x
  disjoint .x. g
  disjoint .x. x
  disjoint U g
  disjoint U x
  disjoint V g
  disjoint V x
  disjoint g ph
  disjoint ph x
  disjoint g y
  disjoint A g
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint .xb y
  disjoint F y
  disjoint G g
  disjoint G y
  disjoint .0. g
  disjoint .0. y
  disjoint P g
  disjoint S y
  disjoint .x. y
  disjoint U y
  disjoint V y
  disjoint X g
  disjoint X y
  disjoint ph y
  assert |- ( ph -> E! g e. B A. x e. V ( S ` ( F .x. x ) ) = ( g .xb ( S ` x ) ) )

  proof
    wph
    cF
    vx
    cv
    #
    c.x
    co
    cS
    cfv
    vg
    cv
    @0
    cS
    cfv
    c.xb
    co
    wceq
    vx
    cV
    wral
    #
    vg
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    wreu
    #
    @1
    vg
    cB
    wreu
    #
    wph
    vx
    @3
    cB
    cC
    @2
    cR
    cS
    c.xb
    c.x
    cU
    vg
    cF
    cH
    cK
    cV
    cW
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
    @2
    eqid
    #
    @3
    eqid
    #
    hdmap14lem14
    wph
    @3
    cB
    wceq
    @4
    @5
    wb
    wph
    cC
    @3
    @2
    cU
    cR
    cH
    cK
    cB
    cW
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.r
    hdmap14lem12.b
    hdmap14lem12.c
    @6
    @7
    hdmap14lem12.k
    lcdsbase
    @1
    vg
    @3
    cB
    reueq1
    syl
    mpbid
end
