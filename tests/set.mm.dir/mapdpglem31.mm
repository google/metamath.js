include "cv.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "eqid.mm"
include "lcd1.mm"
include "oveq1d.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "lcdlmod.mm"
include "csn.mm"
include "wa.mm"
include "simpld.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "weq.mm"
include "mapdpglem30.mm"
include "eqtr2.mm"
include "syl.mm"
include "3eqtr3rd.mm"
include "eqtrd.mm"

theorem mapdpglem31
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
  assume mapdpglem28.ue: |- ( ph -> u e. B )

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
  assert |- ( ph -> h = i )

  proof
    wph
    vh
    cv
    vu
    cv
    #
    vi
    cv
    #
    c.x
    co
    #
    @1
    mapdpglem28.u1
    wph
    cC
    csca
    cfv
    #
    cur
    cfv
    #
    @1
    c.x
    co
    #
    cA
    cur
    cfv
    #
    @1
    c.x
    co
    @1
    @2
    wph
    @4
    @6
    @1
    c.x
    wph
    cC
    @3
    cU
    @6
    cA
    cH
    @4
    cK
    cW
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    @6
    eqid
    mapdpg.c
    @3
    eqid
    #
    @4
    eqid
    #
    mapdpg.k
    lcd1
    oveq1d
    wph
    cC
    clmod
    wcel
    @1
    cF
    wcel
    #
    @5
    @1
    wceq
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
    @9
    cY
    csn
    cN
    cfv
    cM
    cfv
    @1
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
    cG
    @1
    cR
    co
    csn
    cJ
    cfv
    wceq
    wa
    mapdpgem25.i1
    simpld
    c.x
    @4
    @3
    cF
    cC
    @1
    mapdpg.f
    @7
    mapdpglem26.t
    @8
    lmodvs1
    syl2anc
    wph
    @6
    @0
    @1
    c.x
    wph
    vv
    cv
    #
    @6
    wceq
    vv
    vu
    weq
    wa
    @6
    @0
    wceq
    wph
    vv
    vu
    cA
    cB
    cC
    cR
    c.x
    cU
    vh
    vi
    cF
    cG
    cH
    cJ
    cK
    cM
    c.mi
    cN
    cO
    cV
    cW
    cX
    cY
    c.0
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.z
    mapdpg.n
    mapdpg.c
    mapdpg.f
    mapdpg.r
    mapdpg.j
    mapdpg.k
    mapdpg.x
    mapdpg.y
    mapdpg.g
    mapdpg.ne
    mapdpg.e
    mapdpgem25.h1
    mapdpgem25.i1
    mapdpglem26.a
    mapdpglem26.b
    mapdpglem26.t
    mapdpglem26.o
    mapdpglem28.ve
    mapdpglem28.u1
    mapdpglem28.u2
    mapdpglem28.ue
    mapdpglem30
    @10
    @6
    @0
    eqtr2
    syl
    oveq1d
    3eqtr3rd
    eqtrd
end
