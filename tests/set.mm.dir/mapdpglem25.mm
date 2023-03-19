include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "simprd.mm"
include "simpld.mm"
include "eqtr3d.mm"
include "jca.mm"

theorem mapdpglem25
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume mapdpg.h: |- H = ( LHyp ` K )
  assume mapdpg.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdpg.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdpg.v: |- V = ( Base ` U )
  assume mapdpg.s: |- .- = ( -g ` U )
  assume mapdpg.z: |- .0. = ( 0g ` U )
  assume mapdpg.n: |- N = ( LSpan ` U )
  assume mapdpg.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdpg.f: |- F = ( Base ` C )
  assume mapdpg.r: |- R = ( -g ` C )
  assume mapdpg.j: |- J = ( LSpan ` C )
  assume mapdpg.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdpg.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdpg.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdpg.g: |- ( ph -> G e. F )
  assume mapdpg.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdpg.e: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { G } ) )
  assume mapdpgem25.h1: |- ( ph -> ( h e. F /\ ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R h ) } ) ) ) )
  assume mapdpgem25.i1: |- ( ph -> ( i e. F /\ ( ( M ` ( N ` { Y } ) ) = ( J ` { i } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R i ) } ) ) ) )


  assert |- ( ph -> ( ( J ` { h } ) = ( J ` { i } ) /\ ( J ` { ( G R h ) } ) = ( J ` { ( G R i ) } ) ) )

  proof
    wph
    vh
    cv
    #
    csn
    cJ
    cfv
    #
    vi
    cv
    #
    csn
    cJ
    cfv
    #
    wceq
    cG
    @0
    cR
    co
    csn
    cJ
    cfv
    #
    cG
    @2
    cR
    co
    csn
    cJ
    cfv
    #
    wceq
    wph
    cY
    csn
    cN
    cfv
    cM
    cfv
    #
    @1
    @3
    wph
    @6
    @1
    wceq
    #
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    #
    @4
    wceq
    #
    wph
    @0
    cF
    wcel
    @7
    @9
    wa
    mapdpgem25.h1
    simprd
    #
    simpld
    wph
    @6
    @3
    wceq
    #
    @8
    @5
    wceq
    #
    wph
    @2
    cF
    wcel
    @11
    @12
    wa
    mapdpgem25.i1
    simprd
    #
    simpld
    eqtr3d
    wph
    @8
    @4
    @5
    wph
    @7
    @9
    @10
    simprd
    wph
    @11
    @12
    @13
    simprd
    eqtr3d
    jca
end
