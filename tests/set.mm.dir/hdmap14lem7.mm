include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wreu.mm"
include "c0g.mm"
include "wa.mm"
include "clspn.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "simpr.mm"
include "hdmap14lem6.mm"
include "wne.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "hdmap14lem4.mm"
include "pm2.61dane.mm"

theorem hdmap14lem7
  let wph: wff ph
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
  let cX: class X
  let c.0: class .0.
  assume hdmap14lem7.h: |- H = ( LHyp ` K )
  assume hdmap14lem7.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap14lem7.v: |- V = ( Base ` U )
  assume hdmap14lem7.t: |- .x. = ( .s ` U )
  assume hdmap14lem7.o: |- .0. = ( 0g ` U )
  assume hdmap14lem7.r: |- R = ( Scalar ` U )
  assume hdmap14lem7.b: |- B = ( Base ` R )
  assume hdmap14lem7.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap14lem7.e: |- .xb = ( .s ` C )
  assume hdmap14lem7.p: |- P = ( Scalar ` C )
  assume hdmap14lem7.a: |- A = ( Base ` P )
  assume hdmap14lem7.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap14lem7.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap14lem7.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap14lem7.f: |- ( ph -> F e. B )

  disjoint A g
  disjoint C g
  disjoint F g
  disjoint P g
  disjoint R g
  disjoint S g
  disjoint X g
  disjoint g ph
  disjoint .x. g
  disjoint .xb g
  assert |- ( ph -> E! g e. A ( S ` ( F .x. X ) ) = ( g .xb ( S ` X ) ) )

  proof
    wph
    cF
    cX
    c.x
    co
    cS
    cfv
    vg
    cv
    cX
    cS
    cfv
    c.xb
    co
    wceq
    vg
    cA
    wreu
    cF
    cR
    c0g
    cfv
    #
    wph
    cF
    @0
    wceq
    #
    wa
    cA
    cB
    cC
    cP
    cP
    c0g
    cfv
    #
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
    cX
    c.0
    @0
    hdmap14lem7.h
    hdmap14lem7.u
    hdmap14lem7.v
    hdmap14lem7.t
    hdmap14lem7.o
    hdmap14lem7.r
    hdmap14lem7.b
    @0
    eqid
    #
    hdmap14lem7.c
    hdmap14lem7.e
    @3
    eqid
    #
    hdmap14lem7.p
    hdmap14lem7.a
    @2
    eqid
    #
    hdmap14lem7.s
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    hdmap14lem7.k
    adantr
    wph
    cX
    cV
    c.0
    csn
    cdif
    wcel
    #
    @1
    hdmap14lem7.x
    adantr
    wph
    @1
    simpr
    hdmap14lem6
    wph
    cF
    @0
    wne
    #
    wa
    #
    cA
    cB
    cC
    cP
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
    @3
    cV
    cW
    cX
    c.0
    @0
    hdmap14lem7.h
    hdmap14lem7.u
    hdmap14lem7.v
    hdmap14lem7.t
    hdmap14lem7.o
    hdmap14lem7.r
    hdmap14lem7.b
    @4
    hdmap14lem7.c
    hdmap14lem7.e
    @5
    hdmap14lem7.p
    hdmap14lem7.a
    @6
    hdmap14lem7.s
    wph
    @7
    @9
    hdmap14lem7.k
    adantr
    wph
    @8
    @9
    hdmap14lem7.x
    adantr
    @10
    cF
    cB
    wcel
    #
    @9
    cF
    cB
    @0
    csn
    cdif
    wcel
    wph
    @11
    @9
    hdmap14lem7.f
    adantr
    wph
    @9
    simpr
    cF
    cB
    @0
    eldifsn
    sylanbrc
    hdmap14lem4
    pm2.61dane
end
