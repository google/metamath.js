include "cv.mm"
include "cinvr.mm"
include "cfv.mm"
include "co.mm"
include "oveq2d.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "lcdlmod.mm"
include "cdr.mm"
include "wcel.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "mapdpglem11.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "lcdvscl.mm"
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
include "lmodsubdi.mm"
include "cmulr.mm"
include "cur.mm"
include "wceq.mm"
include "drnginvrr.mm"
include "lcd1.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "lcdvsass.mm"
include "lmodvs1.mm"
include "3eqtr3d.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "3eqtrd.mm"

theorem mapdpglem21
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
  assert |- ( ph -> ( ( ( invr ` A ) ` g ) .x. t ) = ( G R E ) )

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
    vt
    cv
    #
    c.x
    co
    @2
    @0
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
    c.x
    co
    @2
    @4
    c.x
    co
    #
    @2
    @5
    c.x
    co
    #
    cR
    co
    #
    cG
    cE
    cR
    co
    #
    wph
    @3
    @6
    @2
    c.x
    mapdpglem4.t4
    oveq2d
    wph
    @2
    c.x
    cC
    csca
    cfv
    #
    @11
    cbs
    cfv
    #
    cR
    cF
    cC
    @4
    @5
    mapdpglem3.f
    mapdpglem3.t
    @11
    eqid
    #
    @12
    eqid
    #
    mapdpglem3.r
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
    @2
    cB
    @12
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
    cB
    wcel
    wph
    cU
    clvec
    wcel
    @16
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
    drnginvrcl
    syl3anc
    #
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
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem.c
    @13
    @14
    mapdpglem.k
    lcdsbase
    eleqtrrd
    wph
    cC
    cB
    cA
    c.x
    cU
    cG
    cH
    cK
    cF
    cW
    @0
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    mapdpglem3.b
    mapdpglem.c
    mapdpglem3.f
    mapdpglem3.t
    mapdpglem.k
    mapdpglem4.g4
    mapdpglem3.g
    lcdvscl
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
    @5
    wph
    @24
    cC
    clss
    cfv
    #
    wcel
    @24
    cF
    wss
    wph
    cC
    @23
    cU
    clss
    cfv
    #
    @25
    cU
    cH
    cK
    cM
    cW
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @26
    eqid
    #
    mapdpglem.c
    @25
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
    @23
    @26
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
    @26
    cN
    cV
    cU
    cY
    mapdpglem.v
    @27
    mapdpglem.n
    lspsncl
    syl2anc
    mapdcl2
    @25
    @24
    cF
    cC
    mapdpglem3.f
    @28
    lssss
    syl
    mapdpglem4.z4
    sseldd
    lmodsubdi
    wph
    @9
    cG
    @8
    cR
    co
    @10
    wph
    @7
    cG
    @8
    cR
    wph
    @0
    @2
    cA
    cmulr
    cfv
    #
    co
    #
    cG
    c.x
    co
    @11
    cur
    cfv
    #
    cG
    c.x
    co
    #
    @7
    cG
    wph
    @30
    @31
    cG
    c.x
    wph
    @30
    cA
    cur
    cfv
    #
    @31
    wph
    @16
    @17
    @18
    @30
    @33
    wceq
    @19
    mapdpglem4.g4
    @20
    cB
    cA
    @29
    @33
    @1
    @0
    c.0
    mapdpglem3.b
    mapdpglem4.z
    @29
    eqid
    #
    @33
    eqid
    #
    @21
    drnginvrr
    syl3anc
    wph
    cC
    @11
    cU
    @33
    cA
    cH
    @31
    cK
    cW
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    @35
    mapdpglem.c
    @13
    @31
    eqid
    #
    mapdpglem.k
    lcd1
    eqtr4d
    oveq1d
    wph
    cC
    cA
    c.x
    @29
    cU
    cF
    cG
    cH
    cK
    cB
    cW
    @2
    @0
    mapdpglem.h
    mapdpglem.u
    mapdpglem3.a
    mapdpglem3.b
    @34
    mapdpglem.c
    mapdpglem3.f
    mapdpglem3.t
    mapdpglem.k
    @22
    mapdpglem4.g4
    mapdpglem3.g
    lcdvsass
    wph
    cC
    clmod
    wcel
    cG
    cF
    wcel
    @32
    cG
    wceq
    @15
    mapdpglem3.g
    c.x
    @31
    @11
    cF
    cC
    cG
    mapdpglem3.f
    @13
    mapdpglem3.t
    @36
    lmodvs1
    syl2anc
    3eqtr3d
    oveq1d
    cE
    @8
    cG
    cR
    mapdpglem17.ep
    oveq2i
    syl6eqr
    3eqtrd
end
