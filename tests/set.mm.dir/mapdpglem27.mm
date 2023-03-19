include "cv.mm"
include "co.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "mapdpglem25.mm"
include "simprd.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "lcdlvec.mm"
include "clmod.mm"
include "wcel.mm"
include "lcdlmod.mm"
include "wa.mm"
include "simpld.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "lspsneq.mm"
include "lcdsbase.mm"
include "lcd0.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "rexeqdv.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem mapdpglem27
  let wph: wff ph
  let vv: setvar v
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
  let vu: setvar u
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

  disjoint ph v
  disjoint h i
  disjoint h v
  disjoint i v
  disjoint B v
  disjoint C v
  disjoint O v
  disjoint .x. v
  disjoint G v
  disjoint R v
  disjoint u v
  disjoint ph u
  disjoint h u
  disjoint i u
  disjoint u v
  disjoint B u
  disjoint C u
  disjoint O u
  disjoint .x. u
  assert |- ( ph -> E. v e. ( B \ { O } ) ( G R h ) = ( v .x. ( G R i ) ) )

  proof
    wph
    cG
    vh
    cv
    #
    cR
    co
    #
    csn
    cJ
    cfv
    #
    cG
    vi
    cv
    #
    cR
    co
    #
    csn
    cJ
    cfv
    #
    wceq
    #
    @1
    vv
    cv
    @4
    c.x
    co
    wceq
    #
    vv
    cB
    cO
    csn
    #
    cdif
    #
    wrex
    #
    wph
    @0
    csn
    cJ
    cfv
    #
    @3
    csn
    cJ
    cfv
    #
    wceq
    @6
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
    simprd
    wph
    @6
    @7
    vv
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    @13
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wrex
    @10
    wph
    @13
    c.x
    vv
    @14
    cJ
    cF
    cC
    @1
    @4
    @15
    mapdpg.f
    @13
    eqid
    #
    @14
    eqid
    #
    @15
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
    cC
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    @0
    cF
    wcel
    #
    @1
    cF
    wcel
    wph
    cC
    cH
    cK
    cW
    mapdpg.h
    mapdpg.c
    mapdpg.k
    lcdlmod
    #
    mapdpg.g
    wph
    @23
    cY
    csn
    cN
    cfv
    cM
    cfv
    #
    @11
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
    @2
    wceq
    wa
    mapdpgem25.h1
    simpld
    cR
    cF
    cC
    cG
    @0
    mapdpg.f
    mapdpg.r
    lmodvsubcl
    syl3anc
    wph
    @21
    @22
    @3
    cF
    wcel
    #
    @4
    cF
    wcel
    @24
    mapdpg.g
    wph
    @27
    @25
    @12
    wceq
    @26
    @5
    wceq
    wa
    mapdpgem25.i1
    simpld
    cR
    cF
    cC
    cG
    @3
    mapdpg.f
    mapdpg.r
    lmodvsubcl
    syl3anc
    lspsneq
    wph
    @7
    vv
    @17
    @9
    wph
    @14
    cB
    @16
    @8
    wph
    cC
    @14
    @13
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
    @18
    @19
    mapdpg.k
    lcdsbase
    wph
    @15
    cO
    wph
    cC
    @13
    cU
    cA
    cH
    cK
    @15
    cW
    cO
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.o
    mapdpg.c
    @18
    @20
    mapdpg.k
    lcd0
    sneqd
    difeq12d
    rexeqdv
    bitrd
    mpbid
end
