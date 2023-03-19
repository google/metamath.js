include "csn.mm"
include "cfv.mm"
include "clsa.mm"
include "wcel.mm"
include "c0g.mm"
include "wne.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lsatlspsn.mm"
include "mapdat.mm"
include "eqeltrrd.mm"
include "lcdlmod.mm"
include "lsatspn0.mm"
include "mpbid.mm"

theorem mapdpglem30a
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
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


  assert |- ( ph -> G =/= ( 0g ` C ) )

  proof
    wph
    cG
    csn
    cJ
    cfv
    #
    cC
    clsa
    cfv
    #
    wcel
    cG
    cC
    c0g
    cfv
    #
    wne
    wph
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    @0
    @1
    mapdpg.e
    wph
    cU
    clsa
    cfv
    #
    @1
    cC
    @3
    cU
    cH
    cK
    cM
    cW
    mapdpg.h
    mapdpg.m
    mapdpg.u
    @4
    eqid
    #
    mapdpg.c
    @1
    eqid
    #
    mapdpg.k
    wph
    @4
    cN
    cV
    cU
    cX
    c.0
    mapdpg.v
    mapdpg.n
    mapdpg.z
    @5
    wph
    cU
    cH
    cK
    cW
    mapdpg.h
    mapdpg.u
    mapdpg.k
    dvhlmod
    mapdpg.x
    lsatlspsn
    mapdat
    eqeltrrd
    wph
    @1
    cJ
    cF
    cC
    cG
    @2
    mapdpg.f
    mapdpg.j
    @2
    eqid
    @6
    wph
    cC
    cH
    cK
    cW
    mapdpg.h
    mapdpg.c
    mapdpg.k
    lcdlmod
    mapdpg.g
    lsatspn0
    mpbid
end
