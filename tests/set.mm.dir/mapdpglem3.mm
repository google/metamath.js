include "cv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cfv.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "csca.mm"
include "cbs.mm"
include "clmod.mm"
include "wb.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "lspsnel.mm"
include "syl2anc.mm"
include "lcdsbase.mm"
include "rexeqdv.mm"
include "bitrd.mm"
include "anbi1d.mm"
include "r19.41v.mm"
include "syl6rbbr.mm"
include "exbidv.mm"
include "df-rex.mm"
include "syl6bbr.mm"
include "clss.mm"
include "csubg.mm"
include "wss.mm"
include "lsssssubg.mm"
include "syl.mm"
include "lspsncl.mm"
include "sseldd.mm"
include "dvhlmod.mm"
include "mapdcl2.mm"
include "lsmelvalm.mm"
include "bitr4d.mm"
include "mpbird.mm"
include "ovex.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "ceqsexv.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "bitr3i.mm"
include "sylibr.mm"

theorem mapdpglem3
  let wph: wff ph
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let c.po: class .(+)
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

  disjoint g z
  disjoint g ph
  disjoint ph z
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
  disjoint w z
  disjoint ph w
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
  assert |- ( ph -> E. g e. B E. z e. ( M ` ( N ` { Y } ) ) t = ( ( g .x. G ) R z ) )

  proof
    wph
    vw
    cv
    #
    vg
    cv
    #
    cG
    c.x
    co
    #
    wceq
    #
    vt
    cv
    #
    @0
    vz
    cv
    #
    cR
    co
    #
    wceq
    #
    vz
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    wrex
    #
    wa
    #
    vg
    cB
    wrex
    #
    vw
    wex
    #
    @4
    @2
    @5
    cR
    co
    #
    wceq
    #
    vz
    @9
    wrex
    #
    vg
    cB
    wrex
    #
    wph
    @13
    @4
    cG
    csn
    cJ
    cfv
    #
    @9
    c.po
    co
    #
    wcel
    #
    wph
    @4
    cX
    csn
    cN
    cfv
    cM
    cfv
    #
    @9
    c.po
    co
    @19
    mapdpglem3.te
    wph
    @21
    @18
    @9
    c.po
    mapdpglem3.e
    oveq1d
    eleqtrd
    wph
    @13
    @10
    vw
    @18
    wrex
    #
    @20
    wph
    @13
    @0
    @18
    wcel
    #
    @10
    wa
    #
    vw
    wex
    @22
    wph
    @12
    @24
    vw
    wph
    @24
    @3
    vg
    cB
    wrex
    #
    @10
    wa
    @12
    wph
    @23
    @25
    @10
    wph
    @23
    @3
    vg
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    @25
    wph
    cC
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    @23
    @28
    wb
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
    mapdpglem3.g
    c.x
    @0
    vg
    @26
    @27
    cJ
    cF
    cC
    cG
    @26
    eqid
    #
    @27
    eqid
    #
    mapdpglem3.f
    mapdpglem3.t
    mapdpglem2.j
    lspsnel
    syl2anc
    wph
    @3
    vg
    @27
    cB
    wph
    cC
    @27
    @26
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
    @32
    @33
    mapdpglem.k
    lcdsbase
    rexeqdv
    bitrd
    anbi1d
    @3
    @10
    vg
    cB
    r19.41v
    syl6rbbr
    exbidv
    @10
    vw
    @18
    df-rex
    syl6bbr
    wph
    vw
    vz
    c.po
    @18
    @9
    cC
    cR
    @4
    mapdpglem3.r
    mapdpglem1.p
    wph
    cC
    clss
    cfv
    #
    cC
    csubg
    cfv
    #
    @18
    wph
    @29
    @34
    @35
    wss
    @31
    @34
    cC
    @34
    eqid
    #
    lsssssubg
    syl
    #
    wph
    @29
    @30
    @18
    @34
    wcel
    @31
    mapdpglem3.g
    @34
    cJ
    cF
    cC
    cG
    mapdpglem3.f
    @36
    mapdpglem2.j
    lspsncl
    syl2anc
    sseldd
    wph
    @34
    @35
    @9
    @37
    wph
    cC
    @8
    cU
    clss
    cfv
    #
    @34
    cU
    cH
    cK
    cM
    cW
    mapdpglem.h
    mapdpglem.m
    mapdpglem.u
    @38
    eqid
    #
    mapdpglem.c
    @36
    mapdpglem.k
    wph
    cU
    clmod
    wcel
    cY
    cV
    wcel
    @8
    @38
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
    @38
    cN
    cV
    cU
    cY
    mapdpglem.v
    @39
    mapdpglem.n
    lspsncl
    syl2anc
    mapdcl2
    sseldd
    lsmelvalm
    bitr4d
    mpbird
    @17
    @11
    vw
    wex
    #
    vg
    cB
    wrex
    @13
    @40
    @16
    vg
    cB
    @10
    @16
    vw
    @2
    @1
    cG
    c.x
    ovex
    @3
    @7
    @15
    vz
    @9
    @3
    @6
    @14
    @4
    @0
    @2
    @5
    cR
    oveq1
    eqeq2d
    rexbidv
    ceqsexv
    rexbii
    @11
    vg
    vw
    cB
    rexcom4
    bitr3i
    sylibr
end
