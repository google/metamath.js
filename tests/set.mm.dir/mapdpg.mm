include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "mapdpglem24.mm"
include "wcel.mm"
include "mapdpglem32.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "sneqd.mm"
include "anbi12d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem mapdpg
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let vh: setvar h
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
  let vg: setvar g
  let vt: setvar t
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v
  let vi: setvar i
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

  disjoint C h
  disjoint F h
  disjoint G h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint R h
  disjoint .- h
  disjoint U h
  disjoint X h
  disjoint Y h
  disjoint h ph
  disjoint g h
  disjoint g t
  disjoint g z
  disjoint C g
  disjoint h t
  disjoint h z
  disjoint t z
  disjoint C t
  disjoint C z
  disjoint F g
  disjoint F t
  disjoint F z
  disjoint G g
  disjoint G t
  disjoint G z
  disjoint J g
  disjoint J t
  disjoint J z
  disjoint M g
  disjoint M t
  disjoint M z
  disjoint N g
  disjoint N t
  disjoint N z
  disjoint R g
  disjoint R t
  disjoint R z
  disjoint .- g
  disjoint .- t
  disjoint .- z
  disjoint U g
  disjoint U z
  disjoint X g
  disjoint X t
  disjoint X z
  disjoint Y g
  disjoint Y t
  disjoint Y z
  disjoint g ph
  disjoint ph t
  disjoint ph z
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint F u
  disjoint F v
  disjoint G u
  disjoint G v
  disjoint J u
  disjoint J v
  disjoint M u
  disjoint M v
  disjoint N u
  disjoint N v
  disjoint R u
  disjoint R v
  disjoint .- u
  disjoint .- v
  disjoint U u
  disjoint U v
  disjoint X u
  disjoint X v
  disjoint Y u
  disjoint Y v
  disjoint h u
  disjoint i u
  disjoint h v
  disjoint i v
  disjoint h i
  disjoint ph u
  disjoint ph v
  disjoint F i
  disjoint G i
  disjoint J i
  disjoint M i
  disjoint N i
  disjoint R i
  disjoint X i
  disjoint .- i
  disjoint i ph
  disjoint Y i
  assert |- ( ph -> E! h e. F ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R h ) } ) ) )

  proof
    wph
    cY
    csn
    cN
    cfv
    cM
    cfv
    #
    vh
    cv
    #
    csn
    #
    cJ
    cfv
    #
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
    cG
    @1
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    vh
    cF
    wrex
    @10
    @0
    vi
    cv
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    @5
    cG
    @11
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    wa
    #
    vh
    vi
    weq
    #
    wi
    #
    vi
    cF
    wral
    vh
    cF
    wral
    @10
    vh
    cF
    wreu
    wph
    cC
    cR
    cU
    vh
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
    mapdpglem24
    wph
    @22
    vh
    vi
    cF
    cF
    wph
    @1
    cF
    wcel
    @11
    cF
    wcel
    wa
    @20
    @21
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
    mapdpglem32
    3exp
    ralrimivv
    @10
    @19
    vh
    vi
    cF
    @21
    @4
    @14
    @9
    @18
    @21
    @3
    @13
    @0
    @21
    @2
    @12
    cJ
    @1
    @11
    sneq
    fveq2d
    eqeq2d
    @21
    @8
    @17
    @5
    @21
    @7
    @16
    cJ
    @21
    @6
    @15
    @1
    @11
    cG
    cR
    oveq2
    sneqd
    fveq2d
    eqeq2d
    anbi12d
    reu4
    sylanbrc
end
