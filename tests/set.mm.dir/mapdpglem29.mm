include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapd11.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "simprd.mm"
include "simpld.mm"
include "3netr3d.mm"

theorem mapdpglem29
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.x: class .x.
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
  let cO: class O
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
  assume mapdpglem26.a: |- A = ( Scalar ` U )
  assume mapdpglem26.b: |- B = ( Base ` A )
  assume mapdpglem26.t: |- .x. = ( .s ` C )
  assume mapdpglem26.o: |- O = ( 0g ` A )
  assume mapdpglem28.ve: |- ( ph -> v e. B )
  assume mapdpglem28.u1: |- ( ph -> h = ( u .x. i ) )
  assume mapdpglem28.u2: |- ( ph -> ( G R h ) = ( v .x. ( G R i ) ) )

  disjoint h i
  disjoint h u
  disjoint h v
  disjoint i u
  disjoint i v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint C u
  disjoint C v
  disjoint O u
  disjoint O v
  disjoint .x. u
  disjoint .x. v
  disjoint G v
  disjoint R v
  assert |- ( ph -> ( J ` { G } ) =/= ( J ` { i } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cG
    csn
    cJ
    cfv
    vi
    cv
    #
    csn
    cJ
    cfv
    #
    wph
    @1
    @3
    wne
    @0
    @2
    wne
    mapdpg.ne
    wph
    @1
    @3
    @0
    @2
    wph
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    cM
    cW
    @0
    @2
    mapdpg.h
    mapdpg.u
    @6
    eqid
    #
    mapdpg.m
    mapdpg.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    @0
    @6
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdpg.h
    mapdpg.u
    mapdpg.k
    dvhlmod
    #
    wph
    cX
    cV
    c.0
    csn
    #
    mapdpg.x
    eldifad
    @6
    cN
    cV
    cU
    cX
    mapdpg.v
    @7
    mapdpg.n
    lspsncl
    syl2anc
    wph
    @8
    cY
    cV
    wcel
    @2
    @6
    wcel
    @9
    wph
    cY
    cV
    @10
    mapdpg.y
    eldifad
    @6
    cN
    cV
    cU
    cY
    mapdpg.v
    @7
    mapdpg.n
    lspsncl
    syl2anc
    mapd11
    necon3bid
    mpbird
    mapdpg.e
    wph
    @3
    @5
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
    @4
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    wph
    @4
    cF
    wcel
    @11
    @12
    wa
    mapdpgem25.i1
    simprd
    simpld
    3netr3d
end
