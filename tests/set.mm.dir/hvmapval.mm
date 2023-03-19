include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "hvmapfval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rexeqbidv.mm"
include "riotabidv.mm"
include "mpteq2dv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem hvmapval
  let wph: wff ph
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vj: setvar j
  let cH: class H
  let cK: class K
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  assume hvmapval.h: |- H = ( LHyp ` K )
  assume hvmapval.u: |- U = ( ( DVecH ` K ) ` W )
  assume hvmapval.o: |- O = ( ( ocH ` K ) ` W )
  assume hvmapval.v: |- V = ( Base ` U )
  assume hvmapval.p: |- .+ = ( +g ` U )
  assume hvmapval.t: |- .x. = ( .s ` U )
  assume hvmapval.z: |- .0. = ( 0g ` U )
  assume hvmapval.s: |- S = ( Scalar ` U )
  assume hvmapval.r: |- R = ( Base ` S )
  assume hvmapval.m: |- M = ( ( HVMap ` K ) ` W )
  assume hvmapval.k: |- ( ph -> ( K e. A /\ W e. H ) )
  assume hvmapval.x: |- ( ph -> X e. ( V \ { .0. } ) )

  disjoint j t
  disjoint j v
  disjoint K j
  disjoint t v
  disjoint K t
  disjoint K v
  disjoint W t
  disjoint O t
  disjoint R j
  disjoint W j
  disjoint W v
  disjoint V v
  disjoint X j
  disjoint X t
  disjoint X v
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint j k
  disjoint j x
  disjoint j w
  disjoint k t
  disjoint k v
  disjoint k x
  disjoint K k
  disjoint t x
  disjoint t w
  disjoint v x
  disjoint v w
  disjoint w x
  disjoint K x
  disjoint K w
  disjoint O w
  disjoint .+ w
  disjoint R w
  disjoint .x. w
  disjoint V w
  disjoint V x
  disjoint W w
  disjoint W x
  disjoint .0. w
  disjoint .0. x
  disjoint O x
  disjoint .+ x
  disjoint R x
  disjoint .x. x
  disjoint X x
  assert |- ( ph -> ( M ` X ) = ( v e. V |-> ( iota_ j e. R E. t e. ( O ` { X } ) v = ( t .+ ( j .x. X ) ) ) ) )

  proof
    wph
    cX
    cM
    cfv
    cX
    vx
    cV
    c.0
    csn
    cdif
    #
    vv
    cV
    vv
    cv
    #
    vt
    cv
    #
    vj
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vt
    @4
    csn
    #
    cO
    cfv
    #
    wrex
    #
    vj
    cR
    crio
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    vv
    cV
    @1
    @2
    @3
    cX
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vt
    cX
    csn
    #
    cO
    cfv
    #
    wrex
    #
    vj
    cR
    crio
    #
    cmpt
    #
    wph
    cX
    cM
    @13
    wph
    vx
    vv
    vt
    cA
    c.pl
    cR
    cS
    c.x
    cU
    vj
    cH
    cK
    cM
    cO
    cV
    cW
    c.0
    hvmapval.h
    hvmapval.u
    hvmapval.o
    hvmapval.v
    hvmapval.p
    hvmapval.t
    hvmapval.z
    hvmapval.s
    hvmapval.r
    hvmapval.m
    hvmapval.k
    hvmapfval
    fveq1d
    wph
    cX
    @0
    wcel
    @22
    cvv
    wcel
    @14
    @22
    wceq
    hvmapval.x
    vv
    cV
    @21
    cV
    cU
    cbs
    cfv
    cvv
    hvmapval.v
    cU
    cbs
    fvex
    eqeltri
    mptex
    vx
    cX
    @12
    @22
    @0
    cvv
    @13
    @4
    cX
    wceq
    #
    vv
    cV
    @11
    @21
    @23
    @10
    @20
    vj
    cR
    @23
    @7
    @17
    vt
    @9
    @19
    @23
    @8
    @18
    cO
    @4
    cX
    sneq
    fveq2d
    @23
    @6
    @16
    @1
    @23
    @5
    @15
    @2
    c.pl
    @4
    cX
    @3
    c.x
    oveq2
    oveq2d
    eqeq2d
    rexeqbidv
    riotabidv
    mpteq2dv
    @13
    eqid
    fvmptg
    sylancl
    eqtrd
end
