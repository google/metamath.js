include "cv.mm"
include "co.mm"
include "oveq2d.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "lcdlmod.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "simpld.mm"
include "lmodsubdi.mm"
include "3eqtr3rd.mm"

theorem mapdpglem28
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
  assert |- ( ph -> ( ( v .x. G ) R ( v .x. i ) ) = ( G R ( u .x. i ) ) )

  proof
    wph
    cG
    vh
    cv
    #
    cR
    co
    vv
    cv
    #
    cG
    vi
    cv
    #
    cR
    co
    #
    c.x
    co
    cG
    vu
    cv
    @2
    c.x
    co
    #
    cR
    co
    @1
    cG
    c.x
    co
    @1
    @2
    c.x
    co
    cR
    co
    mapdpglem28.u2
    wph
    @0
    @4
    cG
    cR
    mapdpglem28.u1
    oveq2d
    wph
    @1
    c.x
    cC
    csca
    cfv
    #
    @5
    cbs
    cfv
    #
    cR
    cF
    cC
    cG
    @2
    mapdpg.f
    mapdpglem26.t
    @5
    eqid
    #
    @6
    eqid
    #
    mapdpg.r
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
    @1
    cB
    @6
    mapdpglem28.ve
    wph
    cC
    @6
    @5
    cU
    cA
    cH
    cK
    cB
    cW
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.b
    mapdpg.c
    @7
    @8
    mapdpg.k
    lcdsbase
    eleqtrrd
    mapdpg.g
    wph
    @2
    cF
    wcel
    cY
    csn
    cN
    cfv
    cM
    cfv
    @2
    csn
    cJ
    cfv
    wceq
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    @3
    csn
    cJ
    cfv
    wceq
    wa
    mapdpgem25.i1
    simpld
    lmodsubdi
    3eqtr3rd
end
