include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "cdif.mm"
include "wrex.mm"
include "mapdpglem25.mm"
include "simpld.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "lcdlvec.mm"
include "wcel.mm"
include "wa.mm"
include "lspsneq.mm"
include "lcdsbase.mm"
include "lcd0.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "rexeqdv.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem mapdpglem26
  let wph: wff ph
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
  let vv: setvar v
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

  disjoint ph u
  disjoint h i
  disjoint h u
  disjoint i u
  disjoint B u
  disjoint C u
  disjoint O u
  disjoint .x. u
  disjoint u v
  disjoint ph v
  disjoint h v
  disjoint i v
  disjoint u v
  disjoint B v
  disjoint C v
  disjoint O v
  disjoint .x. v
  disjoint G v
  disjoint R v
  assert |- ( ph -> E. u e. ( B \ { O } ) h = ( u .x. i ) )

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
    #
    @0
    vu
    cv
    @2
    c.x
    co
    wceq
    #
    vu
    cB
    cO
    csn
    #
    cdif
    #
    wrex
    #
    wph
    @4
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
    cC
    cR
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
    mapdpglem25
    simpld
    wph
    @4
    @5
    vu
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    @11
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wrex
    @8
    wph
    @11
    c.x
    vu
    @12
    cJ
    cF
    cC
    @0
    @2
    @13
    mapdpg.f
    @11
    eqid
    #
    @12
    eqid
    #
    @13
    eqid
    #
    mapdpglem26.t
    mapdpg.j
    wph
    cC
    cH
    cK
    cW
    mapdpg.h
    mapdpg.c
    mapdpg.k
    lcdlvec
    wph
    @0
    cF
    wcel
    cY
    csn
    cN
    cfv
    cM
    cfv
    #
    @1
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
    #
    @9
    wceq
    wa
    mapdpgem25.h1
    simpld
    wph
    @2
    cF
    wcel
    @19
    @3
    wceq
    @20
    @10
    wceq
    wa
    mapdpgem25.i1
    simpld
    lspsneq
    wph
    @5
    vu
    @15
    @7
    wph
    @12
    cB
    @14
    @6
    wph
    cC
    @12
    @11
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
    @16
    @17
    mapdpg.k
    lcdsbase
    wph
    @13
    cO
    wph
    cC
    @11
    cU
    cA
    cH
    cK
    @13
    cW
    cO
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.o
    mapdpg.c
    @16
    @18
    mapdpg.k
    lcd0
    sneqd
    difeq12d
    rexeqdv
    bitrd
    mpbid
end
