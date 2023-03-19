include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "clsm.mm"
include "wrex.mm"
include "wa.mm"
include "eldifad.mm"
include "eqid.mm"
include "mapdpglem2.mm"
include "wcel.mm"
include "w3a.mm"
include "cvsca.mm"
include "csca.mm"
include "cbs.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "mapdpglem3.mm"
include "cinvr.mm"
include "c0g.mm"
include "simp12.mm"
include "wne.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "mapdpglem23.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"
include "rexlimdv3a.mm"

theorem mapdpglem24
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
  assert |- ( ph -> E. h e. F ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R h ) } ) ) )

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
    #
    vt
    cv
    #
    csn
    cJ
    cfv
    wceq
    #
    vt
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cC
    clsm
    cfv
    #
    co
    #
    wrex
    @6
    vh
    cv
    #
    csn
    cJ
    cfv
    wceq
    @0
    cG
    @9
    cR
    co
    csn
    cJ
    cfv
    wceq
    wa
    vh
    cF
    wrex
    #
    wph
    vt
    cC
    @7
    cU
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
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.n
    mapdpg.c
    mapdpg.k
    wph
    cX
    cV
    c.0
    csn
    #
    mapdpg.x
    eldifad
    #
    wph
    cY
    cV
    @11
    mapdpg.y
    eldifad
    #
    @7
    eqid
    #
    mapdpg.j
    mapdpglem2
    wph
    @2
    @10
    vt
    @8
    wph
    @1
    @8
    wcel
    #
    @2
    w3a
    #
    @1
    vg
    cv
    #
    cG
    cC
    cvsca
    cfv
    #
    co
    vz
    cv
    #
    cR
    co
    wceq
    #
    vz
    @6
    wrex
    vg
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    @10
    @16
    vz
    vt
    @21
    @22
    cC
    @7
    cR
    @18
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
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.n
    mapdpg.c
    wph
    @15
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    mapdpg.k
    3ad2ant1
    #
    wph
    @15
    cX
    cV
    wcel
    #
    @2
    @12
    3ad2ant1
    #
    wph
    @15
    cY
    cV
    wcel
    #
    @2
    @13
    3ad2ant1
    #
    @14
    mapdpg.j
    mapdpg.f
    wph
    @15
    @2
    simp2
    @21
    eqid
    #
    @22
    eqid
    #
    @18
    eqid
    #
    mapdpg.r
    wph
    @15
    cG
    cF
    wcel
    #
    @2
    mapdpg.g
    3ad2ant1
    #
    wph
    @15
    @4
    cG
    csn
    cJ
    cfv
    wceq
    #
    @2
    mapdpg.e
    3ad2ant1
    #
    mapdpglem3
    @16
    @20
    @10
    vg
    vz
    @22
    @6
    @16
    @17
    @22
    wcel
    #
    @19
    @6
    wcel
    #
    wa
    #
    @20
    @10
    @16
    @38
    @20
    w3a
    vz
    vt
    @21
    @22
    cC
    @7
    c.0
    cR
    @18
    cU
    vg
    vh
    @17
    @21
    cinvr
    cfv
    cfv
    @19
    @18
    co
    #
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
    @21
    c0g
    cfv
    #
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.n
    mapdpg.c
    @16
    @38
    @23
    @20
    @24
    3ad2ant1
    @16
    @38
    @25
    @20
    @26
    3ad2ant1
    @16
    @38
    @27
    @20
    @28
    3ad2ant1
    @14
    mapdpg.j
    mapdpg.f
    wph
    @15
    @2
    @38
    @20
    simp12
    @29
    @30
    @31
    mapdpg.r
    @16
    @38
    @32
    @20
    @33
    3ad2ant1
    @16
    @38
    @34
    @20
    @35
    3ad2ant1
    mapdpg.z
    @16
    @38
    @3
    @5
    wne
    #
    @20
    wph
    @15
    @41
    @2
    mapdpg.ne
    3ad2ant1
    3ad2ant1
    wph
    @15
    @2
    @38
    @20
    simp13
    @40
    eqid
    @16
    @36
    @37
    @20
    simp2l
    @16
    @36
    @37
    @20
    simp2r
    @16
    @38
    @20
    simp3
    @16
    @38
    cX
    c.0
    wne
    #
    @20
    wph
    @15
    @42
    @2
    wph
    cX
    cV
    @11
    cdif
    #
    wcel
    @42
    mapdpg.x
    cX
    cV
    c.0
    eldifsni
    syl
    3ad2ant1
    3ad2ant1
    @16
    @38
    cY
    c.0
    wne
    #
    @20
    wph
    @15
    @44
    @2
    wph
    cY
    @43
    wcel
    @44
    mapdpg.y
    cY
    cV
    c.0
    eldifsni
    syl
    3ad2ant1
    3ad2ant1
    @39
    eqid
    mapdpglem23
    3exp
    rexlimdvv
    mpd
    rexlimdv3a
    mpd
end
