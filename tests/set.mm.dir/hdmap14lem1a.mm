include "co.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "cmpd.mm"
include "clvec.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "dvhlvec.mm"
include "eqid.mm"
include "lspsnvs.mm"
include "syl121anc.mm"
include "fveq2d.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "hdmap10.mm"
include "3eqtr3rd.mm"

theorem hdmap14lem1a
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
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume hdmap14lem1a.h: |- H = ( LHyp ` K )
  assume hdmap14lem1a.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap14lem1a.v: |- V = ( Base ` U )
  assume hdmap14lem1a.t: |- .x. = ( .s ` U )
  assume hdmap14lem1a.r: |- R = ( Scalar ` U )
  assume hdmap14lem1a.b: |- B = ( Base ` R )
  assume hdmap14lem1a.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap14lem2a.e: |- .xb = ( .s ` C )
  assume hdmap14lem1a.l: |- L = ( LSpan ` C )
  assume hdmap14lem2a.p: |- P = ( Scalar ` C )
  assume hdmap14lem2a.a: |- A = ( Base ` P )
  assume hdmap14lem1a.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap14lem1a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap14lem3a.x: |- ( ph -> X e. V )
  assume hdmap14lem1a.f: |- ( ph -> F e. B )
  assume hdmap14lem1a.z: |- .0. = ( 0g ` R )
  assume hdmap14lem1a.fn: |- ( ph -> F =/= .0. )


  assert |- ( ph -> ( L ` { ( S ` X ) } ) = ( L ` { ( S ` ( F .x. X ) ) } ) )

  proof
    wph
    cF
    cX
    c.x
    co
    #
    csn
    cU
    clspn
    cfv
    #
    cfv
    #
    cW
    cK
    cmpd
    cfv
    cfv
    #
    cfv
    cX
    csn
    @1
    cfv
    #
    @3
    cfv
    @0
    cS
    cfv
    csn
    cL
    cfv
    cX
    cS
    cfv
    csn
    cL
    cfv
    wph
    @2
    @4
    @3
    wph
    cU
    clvec
    wcel
    cF
    cB
    wcel
    #
    cF
    c.0
    wne
    cX
    cV
    wcel
    #
    @2
    @4
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmap14lem1a.h
    hdmap14lem1a.u
    hdmap14lem1a.k
    dvhlvec
    hdmap14lem1a.f
    hdmap14lem1a.fn
    hdmap14lem3a.x
    cF
    c.x
    cR
    cB
    @1
    cV
    cU
    cX
    c.0
    hdmap14lem1a.v
    hdmap14lem1a.r
    hdmap14lem1a.t
    hdmap14lem1a.b
    hdmap14lem1a.z
    @1
    eqid
    #
    lspsnvs
    syl121anc
    fveq2d
    wph
    cC
    cS
    @0
    cU
    cH
    cK
    cL
    @3
    @1
    cV
    cW
    hdmap14lem1a.h
    hdmap14lem1a.u
    hdmap14lem1a.v
    @7
    hdmap14lem1a.c
    hdmap14lem1a.l
    @3
    eqid
    #
    hdmap14lem1a.s
    hdmap14lem1a.k
    wph
    cU
    clmod
    wcel
    @5
    @6
    @0
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap14lem1a.h
    hdmap14lem1a.u
    hdmap14lem1a.k
    dvhlmod
    hdmap14lem1a.f
    hdmap14lem3a.x
    cF
    c.x
    cR
    cB
    cV
    cU
    cX
    hdmap14lem1a.v
    hdmap14lem1a.r
    hdmap14lem1a.t
    hdmap14lem1a.b
    lmodvscl
    syl3anc
    hdmap10
    wph
    cC
    cS
    cX
    cU
    cH
    cK
    cL
    @3
    @1
    cV
    cW
    hdmap14lem1a.h
    hdmap14lem1a.u
    hdmap14lem1a.v
    @7
    hdmap14lem1a.c
    hdmap14lem1a.l
    @8
    hdmap14lem1a.s
    hdmap14lem1a.k
    hdmap14lem3a.x
    hdmap10
    3eqtr3rd
end
