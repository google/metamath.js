include "cv.mm"
include "cinvr.mm"
include "cfv.mm"
include "co.mm"
include "cdr.mm"
include "wcel.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "mapdpglem11.mm"
include "eqid.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
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
include "lcdvscl.mm"
include "syl5eqel.mm"

theorem mapdpglem17N
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
  assert |- ( ph -> E e. F )

  proof
    wph
    cE
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
    cF
    mapdpglem17.ep
    wph
    cC
    cB
    cA
    c.x
    cU
    @3
    cH
    cK
    cF
    cW
    @2
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem.c
    mapdpglem3.f
    mapdpglem3.t
    mapdpglem.k
    wph
    cA
    cdr
    wcel
    #
    @0
    cB
    wcel
    @0
    c.0
    wne
    @2
    cB
    wcel
    wph
    cU
    clvec
    wcel
    @4
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
    cB
    cA
    @1
    @0
    c.0
    mapdpglem3.b
    mapdpglem4.z
    @1
    eqid
    drnginvrcl
    syl3anc
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
    @6
    cC
    clss
    cfv
    #
    wcel
    @6
    cF
    wss
    wph
    cC
    @5
    cU
    clss
    cfv
    #
    @7
    cU
    cH
    cK
    cM
    cW
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @8
    eqid
    #
    mapdpglem.c
    @7
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
    @5
    @8
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
    @8
    cN
    cV
    cU
    cY
    mapdpglem.v
    @9
    mapdpglem.n
    lspsncl
    syl2anc
    mapdcl2
    @7
    @6
    cF
    cC
    mapdpglem3.f
    @10
    lssss
    syl
    mapdpglem4.z4
    sseldd
    lcdvscl
    syl5eqel
end
