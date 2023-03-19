include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "clsa.mm"
include "wcel.mm"
include "c0g.mm"
include "wne.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "simprd.mm"
include "simpld.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lsatlspsn.mm"
include "mapdat.mm"
include "eqeltrrd.mm"
include "lcdlmod.mm"
include "lsatspn0.mm"
include "mpbid.mm"

theorem mapdpglem30b
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


  assert |- ( ph -> i =/= ( 0g ` C ) )

  proof
    wph
    vi
    cv
    #
    csn
    cJ
    cfv
    #
    cC
    clsa
    cfv
    #
    wcel
    @0
    cC
    c0g
    cfv
    #
    wne
    wph
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    @1
    @2
    wph
    @5
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
    cG
    @0
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    wph
    @0
    cF
    wcel
    #
    @6
    @7
    wa
    #
    mapdpgem25.i1
    simprd
    simpld
    wph
    cU
    clsa
    cfv
    #
    @2
    cC
    @4
    cU
    cH
    cK
    cM
    cW
    mapdpg.h
    mapdpg.m
    mapdpg.u
    @10
    eqid
    #
    mapdpg.c
    @2
    eqid
    #
    mapdpg.k
    wph
    @10
    cN
    cV
    cU
    cY
    c.0
    mapdpg.v
    mapdpg.n
    mapdpg.z
    @11
    wph
    cU
    cH
    cK
    cW
    mapdpg.h
    mapdpg.u
    mapdpg.k
    dvhlmod
    mapdpg.y
    lsatlspsn
    mapdat
    eqeltrrd
    wph
    @2
    cJ
    cF
    cC
    @0
    @3
    mapdpg.f
    mapdpg.j
    @3
    eqid
    @12
    wph
    cC
    cH
    cK
    cW
    mapdpg.h
    mapdpg.c
    mapdpg.k
    lcdlmod
    wph
    @8
    @9
    mapdpgem25.i1
    simpld
    lsatspn0
    mpbid
end
