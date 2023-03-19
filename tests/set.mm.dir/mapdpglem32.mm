include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "w3a.mm"
include "cvsca.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "cdif.mm"
include "wrex.mm"
include "weq.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "simp2l.mm"
include "simp3l.mm"
include "jca.mm"
include "simp2r.mm"
include "simp3r.mm"
include "eqid.mm"
include "mapdpglem26.mm"
include "mapdpglem27.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp12r.mm"
include "simp13r.mm"
include "eldifi.mm"
include "adantl.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "mapdpglem31.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem mapdpglem32
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let vh: setvar h
  let vi: setvar i
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
  let vu: setvar u
  let vv: setvar v
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
  disjoint h i
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
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint F u
  disjoint F v
  disjoint G u
  disjoint G v
  disjoint J u
  disjoint J v
  disjoint M u
  disjoint M v
  disjoint N u
  disjoint N v
  disjoint R u
  disjoint R v
  disjoint .- u
  disjoint .- v
  disjoint U u
  disjoint U v
  disjoint X u
  disjoint X v
  disjoint Y u
  disjoint Y v
  disjoint h u
  disjoint i u
  disjoint h v
  disjoint i v
  disjoint ph u
  disjoint ph v
  assert |- ( ( ph /\ ( h e. F /\ i e. F ) /\ ( ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R h ) } ) ) /\ ( ( M ` ( N ` { Y } ) ) = ( J ` { i } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R i ) } ) ) ) ) -> h = i )

  proof
    wph
    vh
    cv
    #
    cF
    wcel
    #
    vi
    cv
    #
    cF
    wcel
    #
    wa
    #
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    @0
    csn
    cJ
    cfv
    wceq
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
    @0
    cR
    co
    #
    csn
    cJ
    cfv
    wceq
    wa
    #
    @6
    @2
    csn
    cJ
    cfv
    wceq
    @7
    cG
    @2
    cR
    co
    #
    csn
    cJ
    cfv
    wceq
    wa
    #
    wa
    #
    w3a
    #
    @0
    vu
    cv
    #
    @2
    cC
    cvsca
    cfv
    #
    co
    wceq
    #
    @8
    vv
    cv
    #
    @10
    @15
    co
    wceq
    #
    wa
    #
    vv
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    @20
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wrex
    vu
    @24
    wrex
    #
    vh
    vi
    weq
    #
    @13
    @16
    vu
    @24
    wrex
    @18
    vv
    @24
    wrex
    @25
    @13
    vu
    @20
    @21
    cC
    cR
    @15
    cU
    vh
    vi
    cF
    cG
    cH
    cJ
    cK
    cM
    c.mi
    cN
    @22
    cV
    cW
    cX
    cY
    c.0
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.z
    mapdpg.n
    mapdpg.c
    mapdpg.f
    mapdpg.r
    mapdpg.j
    wph
    @4
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @12
    mapdpg.k
    3ad2ant1
    #
    wph
    @4
    cX
    cV
    c.0
    csn
    cdif
    #
    wcel
    #
    @12
    mapdpg.x
    3ad2ant1
    #
    wph
    @4
    cY
    @29
    wcel
    #
    @12
    mapdpg.y
    3ad2ant1
    #
    wph
    @4
    cG
    cF
    wcel
    #
    @12
    mapdpg.g
    3ad2ant1
    #
    wph
    @4
    cX
    csn
    cN
    cfv
    #
    @5
    wne
    #
    @12
    mapdpg.ne
    3ad2ant1
    #
    wph
    @4
    @36
    cM
    cfv
    cG
    csn
    cJ
    cfv
    wceq
    #
    @12
    mapdpg.e
    3ad2ant1
    #
    @13
    @1
    @9
    wph
    @1
    @3
    @12
    simp2l
    wph
    @4
    @9
    @11
    simp3l
    jca
    #
    @13
    @3
    @11
    wph
    @1
    @3
    @12
    simp2r
    wph
    @4
    @9
    @11
    simp3r
    jca
    #
    @20
    eqid
    #
    @21
    eqid
    #
    @15
    eqid
    #
    @22
    eqid
    #
    mapdpglem26
    @13
    vv
    @20
    @21
    cC
    cR
    @15
    cU
    vh
    vi
    cF
    cG
    cH
    cJ
    cK
    cM
    c.mi
    cN
    @22
    cV
    cW
    cX
    cY
    c.0
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.z
    mapdpg.n
    mapdpg.c
    mapdpg.f
    mapdpg.r
    mapdpg.j
    @28
    @31
    @33
    @35
    @38
    @40
    @41
    @42
    @43
    @44
    @45
    @46
    mapdpglem27
    @16
    @18
    vu
    vv
    @24
    @24
    reeanv
    sylanbrc
    @13
    @19
    @26
    vu
    vv
    @24
    @24
    @13
    @14
    @24
    wcel
    #
    @17
    @24
    wcel
    #
    wa
    #
    @19
    @26
    @13
    @49
    @19
    w3a
    #
    vv
    vu
    @20
    @21
    cC
    cR
    @15
    cU
    vh
    vi
    cF
    cG
    cH
    cJ
    cK
    cM
    c.mi
    cN
    @22
    cV
    cW
    cX
    cY
    c.0
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.z
    mapdpg.n
    mapdpg.c
    mapdpg.f
    mapdpg.r
    mapdpg.j
    @13
    @49
    @27
    @19
    @28
    3ad2ant1
    @13
    @49
    @30
    @19
    @31
    3ad2ant1
    @13
    @49
    @32
    @19
    @33
    3ad2ant1
    @13
    @49
    @34
    @19
    @35
    3ad2ant1
    @13
    @49
    @37
    @19
    @38
    3ad2ant1
    @13
    @49
    @39
    @19
    @40
    3ad2ant1
    @50
    @1
    @9
    @1
    @3
    wph
    @12
    @49
    @19
    simp12l
    @9
    @11
    wph
    @4
    @49
    @19
    simp13l
    jca
    @50
    @3
    @11
    @1
    @3
    wph
    @12
    @49
    @19
    simp12r
    @9
    @11
    wph
    @4
    @49
    @19
    simp13r
    jca
    @43
    @44
    @45
    @46
    @49
    @13
    @17
    @21
    wcel
    #
    @19
    @48
    @51
    @47
    @17
    @21
    @23
    eldifi
    adantl
    3ad2ant2
    @13
    @49
    @16
    @18
    simp3l
    @13
    @49
    @16
    @18
    simp3r
    @49
    @13
    @14
    @21
    wcel
    #
    @19
    @47
    @52
    @48
    @14
    @21
    @23
    eldifi
    adantr
    3ad2ant2
    mapdpglem31
    3exp
    rexlimdvv
    mpd
end
