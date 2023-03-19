include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "hgmapfval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "cvv.mm"
include "riotaex.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem hgmapval
  let wph: wff ph
  let vy: setvar y
  let vv: setvar v
  let cB: class B
  let cC: class C
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vw: setvar w
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vu: setvar u
  let vx: setvar x
  assume hgmapval.h: |- H = ( LHyp ` K )
  assume hgmapfval.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapfval.v: |- V = ( Base ` U )
  assume hgmapfval.t: |- .x. = ( .s ` U )
  assume hgmapfval.r: |- R = ( Scalar ` U )
  assume hgmapfval.b: |- B = ( Base ` R )
  assume hgmapfval.c: |- C = ( ( LCDual ` K ) ` W )
  assume hgmapfval.s: |- .xb = ( .s ` C )
  assume hgmapfval.m: |- M = ( ( HDMap ` K ) ` W )
  assume hgmapfval.i: |- I = ( ( HGMap ` K ) ` W )
  assume hgmapfval.k: |- ( ph -> ( K e. Y /\ W e. H ) )
  assume hgmapval.x: |- ( ph -> X e. B )

  disjoint v y
  disjoint K v
  disjoint K y
  disjoint B v
  disjoint B y
  disjoint M v
  disjoint M y
  disjoint U v
  disjoint U y
  disjoint V v
  disjoint W v
  disjoint W y
  disjoint X v
  disjoint X y
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint a b
  disjoint a k
  disjoint a m
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint K a
  disjoint b k
  disjoint b m
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint K b
  disjoint k m
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint K m
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint x y
  disjoint K x
  disjoint B a
  disjoint B b
  disjoint B m
  disjoint B u
  disjoint B w
  disjoint B x
  disjoint M a
  disjoint M b
  disjoint M m
  disjoint M u
  disjoint M w
  disjoint M x
  disjoint .xb a
  disjoint .xb b
  disjoint .xb m
  disjoint .xb u
  disjoint .xb w
  disjoint .x. a
  disjoint .x. b
  disjoint .x. m
  disjoint .x. u
  disjoint .x. w
  disjoint U b
  disjoint U m
  disjoint U u
  disjoint U x
  disjoint V a
  disjoint V b
  disjoint V m
  disjoint V u
  disjoint V w
  disjoint W a
  disjoint W b
  disjoint W m
  disjoint W u
  disjoint W w
  disjoint W x
  disjoint .xb x
  disjoint .x. x
  disjoint V x
  disjoint X x
  assert |- ( ph -> ( I ` X ) = ( iota_ y e. B A. v e. V ( M ` ( X .x. v ) ) = ( y .xb ( M ` v ) ) ) )

  proof
    wph
    cX
    cI
    cfv
    cX
    vx
    cB
    vx
    cv
    #
    vv
    cv
    #
    c.x
    co
    #
    cM
    cfv
    #
    vy
    cv
    @1
    cM
    cfv
    c.xb
    co
    #
    wceq
    #
    vv
    cV
    wral
    #
    vy
    cB
    crio
    #
    cmpt
    #
    cfv
    #
    cX
    @1
    c.x
    co
    #
    cM
    cfv
    #
    @4
    wceq
    #
    vv
    cV
    wral
    #
    vy
    cB
    crio
    #
    wph
    cX
    cI
    @8
    wph
    vx
    vy
    vv
    cB
    cC
    cR
    c.xb
    c.x
    cU
    cH
    cI
    cK
    cM
    cV
    cW
    cY
    hgmapval.h
    hgmapfval.u
    hgmapfval.v
    hgmapfval.t
    hgmapfval.r
    hgmapfval.b
    hgmapfval.c
    hgmapfval.s
    hgmapfval.m
    hgmapfval.i
    hgmapfval.k
    hgmapfval
    fveq1d
    wph
    cX
    cB
    wcel
    @14
    cvv
    wcel
    @9
    @14
    wceq
    hgmapval.x
    @13
    vy
    cB
    riotaex
    vx
    cX
    @7
    @14
    cB
    cvv
    @8
    @0
    cX
    wceq
    #
    @6
    @13
    vy
    cB
    @15
    @5
    @12
    vv
    cV
    @15
    @3
    @11
    @4
    @15
    @2
    @10
    cM
    @0
    cX
    @1
    c.x
    oveq1
    fveq2d
    eqeq1d
    ralbidv
    riotabidv
    @8
    eqid
    fvmptg
    sylancl
    eqtrd
end
