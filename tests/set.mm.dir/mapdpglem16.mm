include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "co.mm"
include "simpr.mm"
include "mapdpglem15.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem mapdpglem16
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
  assert |- ( ph -> z =/= ( 0g ` C ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wne
    #
    vz
    cv
    #
    cC
    c0g
    cfv
    #
    wne
    mapdpglem.ne
    wph
    @3
    @4
    @0
    @1
    wph
    @3
    @4
    wceq
    #
    @0
    @1
    wceq
    wph
    @5
    wa
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
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @5
    mapdpglem.k
    adantr
    wph
    cX
    cV
    wcel
    @5
    mapdpglem.x
    adantr
    wph
    cY
    cV
    wcel
    @5
    mapdpglem.y
    adantr
    mapdpglem1.p
    mapdpglem2.j
    mapdpglem3.f
    wph
    vt
    cv
    #
    @0
    cM
    cfv
    #
    @1
    cM
    cfv
    #
    c.po
    co
    wcel
    @5
    mapdpglem3.te
    adantr
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem3.t
    mapdpglem3.r
    wph
    cG
    cF
    wcel
    @5
    mapdpglem3.g
    adantr
    wph
    @7
    cG
    csn
    cJ
    cfv
    wceq
    @5
    mapdpglem3.e
    adantr
    mapdpglem4.q
    wph
    @2
    @5
    mapdpglem.ne
    adantr
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
    @6
    csn
    cJ
    cfv
    wceq
    @5
    mapdpglem4.jt
    adantr
    mapdpglem4.z
    wph
    vg
    cv
    #
    cB
    wcel
    @5
    mapdpglem4.g4
    adantr
    wph
    @3
    @8
    wcel
    @5
    mapdpglem4.z4
    adantr
    wph
    @6
    @9
    cG
    c.x
    co
    @3
    cR
    co
    wceq
    @5
    mapdpglem4.t4
    adantr
    wph
    cX
    cQ
    wne
    @5
    mapdpglem4.xn
    adantr
    wph
    cY
    cQ
    wne
    @5
    mapdpglem12.yn
    adantr
    wph
    @5
    simpr
    mapdpglem15
    ex
    necon3d
    mpd
end
