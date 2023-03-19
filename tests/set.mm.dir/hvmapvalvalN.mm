include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "hvmapval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "cvv.mm"
include "riotaex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem hvmapvalvalN
  let wph: wff ph
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
  let cY: class Y
  let c.0: class .0.
  let vk: setvar k
  let vw: setvar w
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
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
  assume hvmapval.y: |- ( ph -> Y e. V )

  disjoint j t
  disjoint K j
  disjoint K t
  disjoint W t
  disjoint O t
  disjoint R j
  disjoint W j
  disjoint X j
  disjoint X t
  disjoint Y j
  disjoint Y t
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint j k
  disjoint j v
  disjoint j x
  disjoint j w
  disjoint k t
  disjoint k v
  disjoint k x
  disjoint K k
  disjoint t v
  disjoint t x
  disjoint t w
  disjoint v x
  disjoint v w
  disjoint K v
  disjoint w x
  disjoint K x
  disjoint K w
  disjoint O w
  disjoint .+ w
  disjoint R w
  disjoint .x. w
  disjoint V w
  disjoint V x
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint .0. w
  disjoint .0. x
  disjoint O x
  disjoint .+ x
  disjoint R x
  disjoint .x. x
  disjoint V v
  disjoint X v
  disjoint X x
  disjoint .+ y
  disjoint K y
  disjoint O y
  disjoint R y
  disjoint .x. y
  disjoint j y
  disjoint t y
  disjoint Y y
  disjoint V y
  disjoint W y
  disjoint X y
  assert |- ( ph -> ( ( M ` X ) ` Y ) = ( iota_ j e. R E. t e. ( O ` { X } ) Y = ( t .+ ( j .x. X ) ) ) )

  proof
    wph
    cY
    cX
    cM
    cfv
    #
    cfv
    cY
    vy
    cV
    vy
    cv
    #
    vt
    cv
    vj
    cv
    cX
    c.x
    co
    c.pl
    co
    #
    wceq
    #
    vt
    cX
    csn
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
    cfv
    #
    cY
    @2
    wceq
    #
    vt
    @4
    wrex
    #
    vj
    cR
    crio
    #
    wph
    cY
    @0
    @7
    wph
    vy
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
    cX
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
    hvmapval.x
    hvmapval
    fveq1d
    wph
    cY
    cV
    wcel
    @11
    cvv
    wcel
    @8
    @11
    wceq
    hvmapval.y
    @10
    vj
    cR
    riotaex
    vy
    cY
    @6
    @11
    cV
    cvv
    @7
    @1
    cY
    wceq
    #
    @5
    @10
    vj
    cR
    @12
    @3
    @9
    vt
    @4
    @1
    cY
    @2
    eqeq1
    rexbidv
    riotabidv
    @7
    eqid
    fvmptg
    sylancl
    eqtrd
end
