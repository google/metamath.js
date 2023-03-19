include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "wne.mm"
include "wrex.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wreu.mm"
include "eqid.mm"
include "dvh1dim.mm"
include "wcel.mm"
include "w3a.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "csn.mm"
include "cdif.mm"
include "3simpc.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "hdmap14lem7.mm"
include "simpl1.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "hdmap14lem13.mm"
include "reubidva.mm"
include "mpbid.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hdmap14lem14
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
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
  let cG: class G
  let c.0: class .0.
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
  assume hdmap14lem12.p: |- P = ( Scalar ` C )
  assume hdmap14lem12.a: |- A = ( Base ` P )

  disjoint g x
  disjoint A g
  disjoint A x
  disjoint B g
  disjoint C g
  disjoint C x
  disjoint .xb g
  disjoint .xb x
  disjoint F g
  disjoint F x
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
  disjoint g ph
  disjoint ph x
  disjoint g y
  disjoint x y
  disjoint A y
  disjoint .xb y
  disjoint F y
  disjoint G g
  disjoint G y
  disjoint .0. g
  disjoint .0. y
  disjoint S y
  disjoint .x. y
  disjoint U y
  disjoint V y
  disjoint X g
  disjoint X y
  disjoint ph y
  assert |- ( ph -> E! g e. A A. x e. V ( S ` ( F .x. x ) ) = ( g .xb ( S ` x ) ) )

  proof
    wph
    vy
    cv
    #
    cU
    c0g
    cfv
    #
    wne
    #
    vy
    cV
    wrex
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
    #
    @3
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
    cA
    wreu
    #
    wph
    vy
    cU
    cH
    cK
    cV
    cW
    @1
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.v
    @1
    eqid
    #
    hdmap14lem12.k
    dvh1dim
    wph
    @2
    @6
    vy
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
    @4
    @0
    cS
    cfv
    c.xb
    co
    wceq
    #
    vg
    cA
    wreu
    @6
    @9
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
    cV
    cW
    @0
    @1
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.v
    hdmap14lem12.t
    @7
    hdmap14lem12.r
    hdmap14lem12.b
    hdmap14lem12.c
    hdmap14lem12.e
    hdmap14lem12.p
    hdmap14lem12.a
    hdmap14lem12.s
    wph
    @8
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    hdmap14lem12.k
    3ad2ant1
    @9
    @8
    @2
    wa
    @0
    cV
    @1
    csn
    cdif
    wcel
    #
    wph
    @8
    @2
    3simpc
    @0
    cV
    @1
    eldifsn
    sylibr
    #
    wph
    @8
    cF
    cB
    wcel
    #
    @2
    hdmap14lem12.f
    3ad2ant1
    hdmap14lem7
    @9
    @10
    @5
    vg
    cA
    @9
    @4
    cA
    wcel
    #
    wa
    #
    vx
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
    @4
    cH
    cK
    cV
    cW
    @0
    @1
    hdmap14lem12.h
    hdmap14lem12.u
    hdmap14lem12.v
    hdmap14lem12.t
    hdmap14lem12.r
    hdmap14lem12.b
    hdmap14lem12.c
    hdmap14lem12.e
    hdmap14lem12.s
    @16
    wph
    @11
    wph
    @8
    @2
    @15
    simpl1
    #
    hdmap14lem12.k
    syl
    @16
    wph
    @14
    @17
    hdmap14lem12.f
    syl
    hdmap14lem12.p
    hdmap14lem12.a
    @7
    @9
    @12
    @15
    @13
    adantr
    @9
    @15
    simpr
    hdmap14lem13
    reubidva
    mpbid
    rexlimdv3a
    mpd
end
