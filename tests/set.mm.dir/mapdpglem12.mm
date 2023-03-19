include "cv.mm"
include "co.mm"
include "csn.mm"
include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "clss.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdcl2.mm"
include "lspsnid.mm"
include "eleqtrrd.mm"
include "lcdlssvscl.mm"
include "c0g.mm"
include "lss0cl.mm"
include "eqeltrd.mm"
include "lssvsubcl.mm"
include "syl22anc.mm"

theorem mapdpglem12
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
  assume mapdpglem12.g0: |- ( ph -> z = ( 0g ` C ) )

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
  assert |- ( ph -> t e. ( M ` ( N ` { X } ) ) )

  proof
    wph
    vt
    cv
    vg
    cv
    #
    cG
    c.x
    co
    #
    vz
    cv
    #
    cR
    co
    #
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    mapdpglem4.t4
    wph
    cC
    clmod
    wcel
    #
    @5
    cC
    clss
    cfv
    #
    wcel
    #
    @1
    @5
    wcel
    @2
    @5
    wcel
    @3
    @5
    wcel
    wph
    cC
    cH
    cK
    cW
    mapdpglem.h
    mapdpglem.c
    mapdpglem.k
    lcdlmod
    #
    wph
    cC
    @4
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
    @10
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
    cX
    cV
    wcel
    @4
    @10
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
    mapdpglem.x
    @10
    cN
    cV
    cU
    cX
    mapdpglem.v
    @11
    mapdpglem.n
    lspsncl
    syl2anc
    mapdcl2
    #
    wph
    cC
    cB
    @7
    c.x
    cU
    cA
    cH
    cK
    @5
    cF
    cW
    @0
    cG
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem.c
    mapdpglem3.f
    mapdpglem3.t
    @12
    mapdpglem.k
    @13
    mapdpglem4.g4
    wph
    cG
    cG
    csn
    cJ
    cfv
    #
    @5
    wph
    @6
    cG
    cF
    wcel
    cG
    @14
    wcel
    @9
    mapdpglem3.g
    cJ
    cF
    cC
    cG
    mapdpglem3.f
    mapdpglem2.j
    lspsnid
    syl2anc
    mapdpglem3.e
    eleqtrrd
    lcdlssvscl
    wph
    @2
    cC
    c0g
    cfv
    #
    @5
    mapdpglem12.g0
    wph
    @6
    @8
    @15
    @5
    wcel
    @9
    @13
    @7
    @5
    cC
    @15
    @15
    eqid
    @12
    lss0cl
    syl2anc
    eqeltrd
    @7
    @5
    cR
    cC
    @1
    @2
    mapdpglem3.r
    @12
    lssvsubcl
    syl22anc
    eqeltrd
end
