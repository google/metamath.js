include "cv.mm"
include "cinvr.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wne.mm"
include "csca.mm"
include "cdr.mm"
include "wcel.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "mapdpglem11.mm"
include "eqid.mm"
include "drnginvrn0.mm"
include "syl3anc.mm"
include "lcd0.mm"
include "neeqtrrd.mm"
include "mapdpglem16.mm"
include "cbs.mm"
include "lcdlvec.mm"
include "drnginvrcl.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "csn.mm"
include "clss.mm"
include "wss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdcl2.mm"
include "lssss.mm"
include "sseldd.mm"
include "lvecvsn0.mm"
include "mpbir2and.mm"
include "3netr4g.mm"

theorem mapdpglem18
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
  assert |- ( ph -> E =/= ( 0g ` C ) )

  proof
    wph
    vg
    cv
    #
    cA
    cinvr
    cfv
    #
    cfv
    #
    vz
    cv
    #
    c.x
    co
    #
    cC
    c0g
    cfv
    #
    cE
    @5
    wph
    @4
    @5
    wne
    @2
    cC
    csca
    cfv
    #
    c0g
    cfv
    #
    wne
    @3
    @5
    wne
    wph
    @2
    c.0
    @7
    wph
    cA
    cdr
    wcel
    #
    @0
    cB
    wcel
    #
    @0
    c.0
    wne
    #
    @2
    c.0
    wne
    wph
    cU
    clvec
    wcel
    @8
    wph
    cU
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.u
    mapdpglem.k
    dvhlvec
    cA
    cU
    mapdpglem3.a
    lvecdrng
    syl
    #
    mapdpglem4.g4
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
    mapdpglem11
    #
    cB
    cA
    @1
    @0
    c.0
    mapdpglem3.b
    mapdpglem4.z
    @1
    eqid
    #
    drnginvrn0
    syl3anc
    wph
    cC
    @6
    cU
    cA
    cH
    cK
    @7
    cW
    c.0
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    mapdpglem4.z
    mapdpglem.c
    @6
    eqid
    #
    @7
    eqid
    #
    mapdpglem.k
    lcd0
    neeqtrrd
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
    mapdpglem16
    wph
    @2
    c.x
    @6
    @6
    cbs
    cfv
    #
    @7
    cF
    cC
    @3
    @5
    mapdpglem3.f
    mapdpglem3.t
    @14
    @16
    eqid
    #
    @15
    @5
    eqid
    #
    wph
    cC
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.c
    mapdpglem.k
    lcdlvec
    wph
    @2
    cB
    @16
    wph
    @8
    @9
    @10
    @2
    cB
    wcel
    @11
    mapdpglem4.g4
    @12
    cB
    cA
    @1
    @0
    c.0
    mapdpglem3.b
    mapdpglem4.z
    @13
    drnginvrcl
    syl3anc
    wph
    cC
    @16
    @6
    cU
    cA
    cH
    cK
    cB
    cW
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem.c
    @14
    @17
    mapdpglem.k
    lcdsbase
    eleqtrrd
    wph
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cF
    @3
    wph
    @20
    cC
    clss
    cfv
    #
    wcel
    @20
    cF
    wss
    wph
    cC
    @19
    cU
    clss
    cfv
    #
    @21
    cU
    cH
    cK
    cM
    cW
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @22
    eqid
    #
    mapdpglem.c
    @21
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
    @19
    @22
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
    @22
    cN
    cV
    cU
    cY
    mapdpglem.v
    @23
    mapdpglem.n
    lspsncl
    syl2anc
    mapdcl2
    @21
    @20
    cF
    cC
    mapdpglem3.f
    @24
    lssss
    syl
    mapdpglem4.z4
    sseldd
    lvecvsn0
    mpbir2and
    mapdpglem17.ep
    @18
    3netr4g
end
