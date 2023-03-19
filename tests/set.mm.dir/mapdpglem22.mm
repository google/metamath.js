include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "cinvr.mm"
include "clvec.mm"
include "wcel.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "wne.mm"
include "wceq.mm"
include "lcdlvec.mm"
include "cdr.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "mapdpglem11.mm"
include "eqid.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "drnginvrn0.mm"
include "lcd0.mm"
include "neeqtrrd.mm"
include "mapdpglem2a.mm"
include "lspsnvs.mm"
include "syl121anc.mm"
include "mapdpglem21.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"

theorem mapdpglem22
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
  assert |- ( ph -> ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R E ) } ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    vt
    cv
    #
    csn
    cJ
    cfv
    #
    vg
    cv
    #
    cA
    cinvr
    cfv
    #
    cfv
    #
    @0
    c.x
    co
    #
    csn
    #
    cJ
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
    mapdpglem4.jt
    wph
    cC
    clvec
    wcel
    @4
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @4
    @10
    c0g
    cfv
    #
    wne
    @0
    cF
    wcel
    @7
    @1
    wceq
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
    @4
    cB
    @11
    wph
    cA
    cdr
    wcel
    #
    @2
    cB
    wcel
    #
    @2
    c.0
    wne
    #
    @4
    cB
    wcel
    wph
    cU
    clvec
    wcel
    @13
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
    @3
    @2
    c.0
    mapdpglem3.b
    mapdpglem4.z
    @3
    eqid
    #
    drnginvrcl
    syl3anc
    wph
    cC
    @11
    @10
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
    @10
    eqid
    #
    @11
    eqid
    #
    mapdpglem.k
    lcdsbase
    eleqtrrd
    wph
    @4
    c.0
    @12
    wph
    @13
    @14
    @15
    @4
    c.0
    wne
    @16
    mapdpglem4.g4
    @17
    cB
    cA
    @3
    @2
    c.0
    mapdpglem3.b
    mapdpglem4.z
    @18
    drnginvrn0
    syl3anc
    wph
    cC
    @10
    cU
    cA
    cH
    cK
    @12
    cW
    c.0
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    mapdpglem4.z
    mapdpglem.c
    @19
    @12
    eqid
    #
    mapdpglem.k
    lcd0
    neeqtrrd
    wph
    vt
    cC
    c.po
    cU
    cF
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
    mapdpglem2a
    @4
    c.x
    @10
    @11
    cJ
    cF
    cC
    @0
    @12
    mapdpglem3.f
    @19
    mapdpglem3.t
    @20
    @21
    mapdpglem2.j
    lspsnvs
    syl121anc
    wph
    @6
    @9
    cJ
    wph
    @5
    @8
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
    mapdpglem21
    sneqd
    fveq2d
    3eqtr2d
end
