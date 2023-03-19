include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "clsa.mm"
include "wcel.mm"
include "c0g.mm"
include "wne.mm"
include "co.mm"
include "eqid.mm"
include "mapdpglem4N.mm"
include "dvhlmod.mm"
include "clmod.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "lsatspn0.mm"
include "mpbird.mm"
include "mapdat.mm"
include "eqeltrrd.mm"
include "lcdlmod.mm"
include "mapdpglem2a.mm"
include "mpbid.mm"

theorem mapdpglem5N
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cU: class U
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
  let vg: setvar g
  let vw: setvar w
  let vz: setvar z
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

  disjoint .- t
  disjoint C t
  disjoint J t
  disjoint M t
  disjoint N t
  disjoint X t
  disjoint Y t
  disjoint g w
  disjoint B g
  disjoint B w
  disjoint g z
  disjoint C g
  disjoint w z
  disjoint C w
  disjoint C z
  disjoint F g
  disjoint G g
  disjoint G w
  disjoint G z
  disjoint J g
  disjoint J w
  disjoint J z
  disjoint M g
  disjoint M w
  disjoint M z
  disjoint N g
  disjoint N w
  disjoint N z
  disjoint R g
  disjoint R w
  disjoint R z
  disjoint .x. g
  disjoint .x. w
  disjoint .x. z
  disjoint Y g
  disjoint Y w
  disjoint Y z
  disjoint g t
  disjoint t w
  disjoint t z
  assert |- ( ph -> t =/= ( 0g ` C ) )

  proof
    wph
    vt
    cv
    #
    csn
    cJ
    cfv
    #
    cC
    clsa
    cfv
    #
    wcel
    @0
    cC
    c0g
    cfv
    #
    wne
    wph
    cX
    cY
    c.mi
    co
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    @1
    @2
    mapdpglem4.jt
    wph
    cU
    clsa
    cfv
    #
    @2
    cC
    @5
    cU
    cH
    cK
    cM
    cW
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @6
    eqid
    #
    mapdpglem.c
    @2
    eqid
    #
    mapdpglem.k
    wph
    @5
    @6
    wcel
    @4
    cQ
    wne
    wph
    vt
    cA
    cB
    cC
    c.po
    cQ
    cR
    c.x
    cU
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
    mapdpglem4N
    wph
    @6
    cN
    cV
    cU
    @4
    cQ
    mapdpglem.v
    mapdpglem.n
    mapdpglem4.q
    @7
    wph
    cU
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.u
    mapdpglem.k
    dvhlmod
    #
    wph
    cU
    clmod
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    @4
    cV
    wcel
    @9
    mapdpglem.x
    mapdpglem.y
    c.mi
    cV
    cU
    cX
    cY
    mapdpglem.v
    mapdpglem.s
    lmodvsubcl
    syl3anc
    lsatspn0
    mpbird
    mapdat
    eqeltrrd
    wph
    @2
    cJ
    cF
    cC
    @0
    @3
    mapdpglem3.f
    mapdpglem2.j
    @3
    eqid
    @8
    wph
    cC
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.c
    mapdpglem.k
    lcdlmod
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
    lsatspn0
    mpbid
end
