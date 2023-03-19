include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdcl2.mm"
include "mapdpglem19.mm"
include "lssel.mm"
include "mapdpglem20.mm"
include "mapdpglem22.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "sneqd.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem mapdpglem23
  let wph: wff ph
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cE: class E
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
  let vw: setvar w
  assume mapdpglem.h: |- H = ( LHyp ` K )
  assume mapdpglem.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdpglem.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdpglem.v: |- V = ( Base ` U )
  assume mapdpglem.s: |- .- = ( -g ` U )
  assume mapdpglem.n: |- N = ( LSpan ` U )
  assume mapdpglem.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdpglem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdpglem.x: |- ( ph -> X e. V )
  assume mapdpglem.y: |- ( ph -> Y e. V )
  assume mapdpglem1.p: |- .(+) = ( LSSum ` C )
  assume mapdpglem2.j: |- J = ( LSpan ` C )
  assume mapdpglem3.f: |- F = ( Base ` C )
  assume mapdpglem3.te: |- ( ph -> t e. ( ( M ` ( N ` { X } ) ) .(+) ( M ` ( N ` { Y } ) ) ) )
  assume mapdpglem3.a: |- A = ( Scalar ` U )
  assume mapdpglem3.b: |- B = ( Base ` A )
  assume mapdpglem3.t: |- .x. = ( .s ` C )
  assume mapdpglem3.r: |- R = ( -g ` C )
  assume mapdpglem3.g: |- ( ph -> G e. F )
  assume mapdpglem3.e: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { G } ) )
  assume mapdpglem4.q: |- Q = ( 0g ` U )
  assume mapdpglem.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdpglem4.jt: |- ( ph -> ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { t } ) )
  assume mapdpglem4.z: |- .0. = ( 0g ` A )
  assume mapdpglem4.g4: |- ( ph -> g e. B )
  assume mapdpglem4.z4: |- ( ph -> z e. ( M ` ( N ` { Y } ) ) )
  assume mapdpglem4.t4: |- ( ph -> t = ( ( g .x. G ) R z ) )
  assume mapdpglem4.xn: |- ( ph -> X =/= Q )
  assume mapdpglem12.yn: |- ( ph -> Y =/= Q )
  assume mapdpglem17.ep: |- E = ( ( ( invr ` A ) ` g ) .x. z )

  disjoint .- t
  disjoint C t
  disjoint J t
  disjoint M t
  disjoint N t
  disjoint X t
  disjoint Y t
  disjoint B g
  disjoint g z
  disjoint C g
  disjoint C z
  disjoint F g
  disjoint G g
  disjoint G z
  disjoint J g
  disjoint J z
  disjoint M g
  disjoint M z
  disjoint N g
  disjoint N z
  disjoint R g
  disjoint R z
  disjoint .x. g
  disjoint .x. z
  disjoint Y g
  disjoint Y z
  disjoint g t
  disjoint t z
  disjoint E h
  disjoint F h
  disjoint G h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint R h
  disjoint .- h
  disjoint X h
  disjoint Y h
  disjoint g w
  disjoint B w
  disjoint w z
  disjoint C w
  disjoint G w
  disjoint J w
  disjoint M w
  disjoint N w
  disjoint R w
  disjoint .x. w
  disjoint Y w
  disjoint t w
  assert |- ( ph -> E. h e. F ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R h ) } ) ) )

  proof
    wph
    cE
    cF
    wcel
    #
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cE
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
    cE
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
    @2
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
    @6
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
    vh
    cF
    wrex
    wph
    @2
    cC
    clss
    cfv
    #
    wcel
    cE
    @2
    wcel
    @0
    wph
    cC
    @1
    cU
    clss
    cfv
    #
    @20
    cU
    cH
    cK
    cM
    cW
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @21
    eqid
    #
    mapdpglem.c
    @20
    eqid
    #
    mapdpglem.k
    wph
    cU
    clmod
    wcel
    cY
    cV
    wcel
    @1
    @21
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.u
    mapdpglem.k
    dvhlmod
    mapdpglem.y
    @21
    cN
    cV
    cU
    cY
    mapdpglem.v
    @22
    mapdpglem.n
    lspsncl
    syl2anc
    mapdcl2
    wph
    vz
    vt
    cA
    cB
    cC
    c.po
    cQ
    cR
    c.x
    cU
    vg
    cE
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
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    mapdpglem.v
    mapdpglem.s
    mapdpglem.n
    mapdpglem.c
    mapdpglem.k
    mapdpglem.x
    mapdpglem.y
    mapdpglem1.p
    mapdpglem2.j
    mapdpglem3.f
    mapdpglem3.te
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem3.t
    mapdpglem3.r
    mapdpglem3.g
    mapdpglem3.e
    mapdpglem4.q
    mapdpglem.ne
    mapdpglem4.jt
    mapdpglem4.z
    mapdpglem4.g4
    mapdpglem4.z4
    mapdpglem4.t4
    mapdpglem4.xn
    mapdpglem12.yn
    mapdpglem17.ep
    mapdpglem19
    @20
    @2
    cF
    cC
    cE
    mapdpglem3.f
    @23
    lssel
    syl2anc
    wph
    vz
    vt
    cA
    cB
    cC
    c.po
    cQ
    cR
    c.x
    cU
    vg
    cE
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
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    mapdpglem.v
    mapdpglem.s
    mapdpglem.n
    mapdpglem.c
    mapdpglem.k
    mapdpglem.x
    mapdpglem.y
    mapdpglem1.p
    mapdpglem2.j
    mapdpglem3.f
    mapdpglem3.te
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem3.t
    mapdpglem3.r
    mapdpglem3.g
    mapdpglem3.e
    mapdpglem4.q
    mapdpglem.ne
    mapdpglem4.jt
    mapdpglem4.z
    mapdpglem4.g4
    mapdpglem4.z4
    mapdpglem4.t4
    mapdpglem4.xn
    mapdpglem12.yn
    mapdpglem17.ep
    mapdpglem20
    wph
    vz
    vt
    cA
    cB
    cC
    c.po
    cQ
    cR
    c.x
    cU
    vg
    cE
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
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    mapdpglem.v
    mapdpglem.s
    mapdpglem.n
    mapdpglem.c
    mapdpglem.k
    mapdpglem.x
    mapdpglem.y
    mapdpglem1.p
    mapdpglem2.j
    mapdpglem3.f
    mapdpglem3.te
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem3.t
    mapdpglem3.r
    mapdpglem3.g
    mapdpglem3.e
    mapdpglem4.q
    mapdpglem.ne
    mapdpglem4.jt
    mapdpglem4.z
    mapdpglem4.g4
    mapdpglem4.z4
    mapdpglem4.t4
    mapdpglem4.xn
    mapdpglem12.yn
    mapdpglem17.ep
    mapdpglem22
    @19
    @5
    @10
    wa
    vh
    cE
    cF
    @11
    cE
    wceq
    #
    @14
    @5
    @18
    @10
    @24
    @13
    @4
    @2
    @24
    @12
    @3
    cJ
    @11
    cE
    sneq
    fveq2d
    eqeq2d
    @24
    @17
    @9
    @6
    @24
    @16
    @8
    cJ
    @24
    @15
    @7
    @11
    cE
    cG
    cR
    oveq2
    sneqd
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
end
