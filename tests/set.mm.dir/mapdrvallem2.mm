include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "eleq1.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lcfl8b.mm"
include "cvsca.mm"
include "co.mm"
include "wb.mm"
include "wex.mm"
include "csca.mm"
include "cbs.mm"
include "ciun.mm"
include "simp1l3.mm"
include "eqimss2.mm"
include "3ad2ant3.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lcfl1lem.mm"
include "simplbi.mm"
include "3ad2ant2.mm"
include "lkrssv.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "eldifi.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "sseldd.mm"
include "syl6eleq.mm"
include "eliun.mm"
include "sylib.mm"
include "eqid.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "ad2antrr.mm"
include "simp1l1.mm"
include "syl.mm"
include "sseld.mm"
include "syl6.mm"
include "mpd.mm"
include "simpll3.mm"
include "lspsnel5a.mm"
include "simpll2.mm"
include "lsatlspsn.mm"
include "dochsat0.mm"
include "lsatcmp2.mm"
include "mpbid.mm"
include "eqtr2d.mm"
include "cdih.mm"
include "crn.mm"
include "sselda.mm"
include "lcfl5.mm"
include "simp1l2.mm"
include "doch11.mm"
include "eqlkr4.mm"
include "ex.mm"
include "reximdva.mm"
include "reximi.mm"
include "rexcom.mm"
include "df-rex.mm"
include "rexbii.mm"
include "bitri.mm"
include "wi.mm"
include "simplr.mm"
include "simprl.mm"
include "ldualssvscl.mm"
include "biimpr.mm"
include "ad2antll.mm"
include "exlimdv.mm"
include "rexlimdva.mm"
include "rexlimdv3a.mm"
include "lduallmod.mm"
include "lss0cl.mm"
include "pm2.61ne.mm"
include "rabssdv.mm"

theorem mapdrvallem2
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vr: setvar r
  let vx: setvar x
  let vi: setvar i
  assume mapdrval.h: |- H = ( LHyp ` K )
  assume mapdrval.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdrval.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdrval.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdrval.s: |- S = ( LSubSp ` U )
  assume mapdrval.f: |- F = ( LFnl ` U )
  assume mapdrval.l: |- L = ( LKer ` U )
  assume mapdrval.d: |- D = ( LDual ` U )
  assume mapdrval.t: |- T = ( LSubSp ` D )
  assume mapdrval.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }
  assume mapdrval.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdrval.r: |- ( ph -> R e. T )
  assume mapdrval.e: |- ( ph -> R C_ C )
  assume mapdrval.q: |- Q = U_ h e. R ( O ` ( L ` h ) )
  assume mapdrval.v: |- V = ( Base ` U )
  assume mapdrvallem2.a: |- A = ( LSAtoms ` U )
  assume mapdrvallem2.n: |- N = ( LSpan ` U )
  assume mapdrvallem2.z: |- .0. = ( 0g ` U )
  assume mapdrvallem2.y: |- Y = ( 0g ` D )

  disjoint C h
  disjoint N h
  disjoint Q h
  disjoint U h
  disjoint V h
  disjoint Y h
  disjoint .0. h
  disjoint h ph
  disjoint f g
  disjoint C f
  disjoint f g
  disjoint F f
  disjoint F g
  disjoint K f
  disjoint g h
  disjoint L g
  disjoint L h
  disjoint O g
  disjoint O h
  disjoint Q f
  disjoint f h
  disjoint R f
  disjoint R h
  disjoint U g
  disjoint W f
  disjoint f ph
  disjoint h r
  disjoint h x
  disjoint r x
  disjoint C r
  disjoint C x
  disjoint F r
  disjoint L r
  disjoint L x
  disjoint N r
  disjoint O r
  disjoint O x
  disjoint Q r
  disjoint Q x
  disjoint R r
  disjoint R x
  disjoint U r
  disjoint U x
  disjoint V r
  disjoint V x
  disjoint Y r
  disjoint Y x
  disjoint .0. r
  disjoint ph r
  disjoint ph x
  disjoint f r
  disjoint f x
  disjoint g r
  disjoint g x
  disjoint f i
  disjoint C i
  disjoint D i
  disjoint g i
  disjoint h i
  disjoint L i
  disjoint O i
  disjoint Q i
  disjoint R i
  disjoint U i
  disjoint V i
  disjoint i ph
  assert |- ( ph -> { f e. C | ( O ` ( L ` f ) ) C_ Q } C_ R )

  proof
    wph
    vf
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    cQ
    wss
    #
    vf
    cC
    cR
    wph
    @0
    cC
    wcel
    #
    @3
    w3a
    #
    @0
    cR
    wcel
    #
    cY
    cR
    wcel
    #
    @0
    cY
    @0
    cY
    cR
    eleq1
    @5
    @0
    cY
    wne
    #
    wa
    #
    @2
    vx
    cv
    #
    csn
    cN
    cfv
    #
    wceq
    #
    vx
    cV
    c.0
    csn
    #
    cdif
    #
    wrex
    @6
    @9
    vx
    cC
    cD
    cU
    vg
    cF
    @0
    cH
    cK
    cL
    cN
    cO
    cV
    cW
    cY
    c.0
    mapdrval.h
    mapdrval.o
    mapdrval.u
    mapdrval.v
    mapdrvallem2.n
    mapdrvallem2.z
    mapdrval.f
    mapdrval.l
    mapdrval.d
    mapdrvallem2.y
    mapdrval.c
    @5
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @8
    wph
    @4
    @15
    @3
    mapdrval.k
    3ad2ant1
    adantr
    #
    @9
    @4
    @8
    @0
    cC
    cY
    csn
    cdif
    wcel
    wph
    @4
    @3
    @8
    simpl2
    @5
    @8
    simpr
    @0
    cC
    cY
    eldifsn
    sylanbrc
    lcfl8b
    @9
    @12
    @6
    vx
    @14
    @9
    @10
    @14
    wcel
    #
    @12
    w3a
    #
    vh
    cv
    #
    cR
    wcel
    #
    @6
    vr
    cv
    #
    @19
    cD
    cvsca
    cfv
    #
    co
    #
    cR
    wcel
    #
    wb
    #
    wa
    #
    vh
    wex
    #
    vr
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    @6
    @18
    @0
    @23
    wceq
    #
    vr
    @29
    wrex
    #
    vh
    cR
    wrex
    #
    @30
    @18
    @10
    @19
    cL
    cfv
    #
    cO
    cfv
    #
    wcel
    #
    vh
    cR
    wrex
    #
    @33
    @18
    @10
    vh
    cR
    @35
    ciun
    #
    wcel
    @37
    @18
    @10
    cQ
    @38
    @18
    @2
    cQ
    @10
    wph
    @4
    @3
    @8
    @17
    @12
    simp1l3
    @18
    @10
    @2
    wcel
    @11
    @2
    wss
    #
    @12
    @9
    @39
    @17
    @11
    @2
    eqimss2
    3ad2ant3
    @18
    cS
    @2
    cN
    cV
    cU
    @10
    mapdrval.v
    mapdrval.s
    mapdrvallem2.n
    @9
    @17
    cU
    clmod
    wcel
    #
    @12
    @5
    @40
    @8
    wph
    @4
    @40
    @3
    wph
    cU
    cH
    cK
    cW
    mapdrval.h
    mapdrval.u
    mapdrval.k
    dvhlmod
    #
    3ad2ant1
    adantr
    #
    3ad2ant1
    #
    @18
    @15
    @1
    cV
    wss
    @2
    cS
    wcel
    @9
    @17
    @15
    @12
    @16
    3ad2ant1
    #
    @18
    cF
    @0
    cL
    cV
    cU
    mapdrval.v
    mapdrval.f
    mapdrval.l
    @43
    @9
    @17
    @0
    cF
    wcel
    #
    @12
    @5
    @45
    @8
    @4
    wph
    @45
    @3
    @4
    @45
    @2
    cO
    cfv
    @1
    wceq
    cC
    vg
    cF
    @0
    cL
    cO
    mapdrval.c
    lcfl1lem
    simplbi
    3ad2ant2
    adantr
    3ad2ant1
    #
    lkrssv
    cS
    cU
    cH
    cK
    cO
    cV
    cW
    @1
    mapdrval.h
    mapdrval.u
    mapdrval.v
    mapdrval.s
    mapdrval.o
    dochlss
    syl2anc
    @17
    @9
    @10
    cV
    wcel
    @12
    @10
    cV
    @13
    eldifi
    3ad2ant2
    lspsnel5
    mpbird
    sseldd
    mapdrval.q
    syl6eleq
    vh
    @10
    cR
    @35
    eliun
    sylib
    @18
    @36
    @32
    vh
    cR
    @18
    @20
    wa
    #
    @36
    @32
    @47
    @36
    wa
    #
    cD
    @29
    @28
    @22
    cF
    @19
    @0
    cL
    cU
    vr
    @28
    eqid
    #
    @29
    eqid
    #
    mapdrval.f
    mapdrval.l
    mapdrval.d
    @22
    eqid
    #
    @18
    cU
    clvec
    wcel
    #
    @20
    @36
    @9
    @17
    @52
    @12
    @5
    @52
    @8
    wph
    @4
    @52
    @3
    wph
    cU
    cH
    cK
    cW
    mapdrval.h
    mapdrval.u
    mapdrval.k
    dvhlvec
    3ad2ant1
    adantr
    3ad2ant1
    ad2antrr
    #
    @47
    @19
    cF
    wcel
    #
    @36
    @47
    @20
    @54
    @18
    @20
    simpr
    @47
    @20
    @19
    cC
    wcel
    #
    @54
    @47
    cR
    cC
    @19
    @47
    wph
    cR
    cC
    wss
    #
    @18
    wph
    @20
    wph
    @4
    @3
    @8
    @17
    @12
    simp1l1
    #
    adantr
    mapdrval.e
    syl
    sseld
    @55
    @54
    @35
    cO
    cfv
    @34
    wceq
    cC
    vg
    cF
    @19
    cL
    cO
    mapdrval.c
    lcfl1lem
    simplbi
    syl6
    mpd
    adantr
    #
    @18
    @45
    @20
    @36
    @46
    ad2antrr
    #
    @48
    @35
    @2
    wceq
    @34
    @1
    wceq
    @48
    @2
    @11
    @35
    @9
    @17
    @12
    @20
    @36
    simpll3
    @48
    @11
    @35
    wss
    @11
    @35
    wceq
    @48
    cS
    @35
    cN
    cU
    @10
    mapdrval.s
    mapdrvallem2.n
    @18
    @40
    @20
    @36
    @43
    ad2antrr
    #
    @48
    @15
    @34
    cV
    wss
    @35
    cS
    wcel
    @18
    @15
    @20
    @36
    @44
    ad2antrr
    #
    @48
    cF
    @19
    cL
    cV
    cU
    mapdrval.v
    mapdrval.f
    mapdrval.l
    @60
    @58
    lkrssv
    cS
    cU
    cH
    cK
    cO
    cV
    cW
    @34
    mapdrval.h
    mapdrval.u
    mapdrval.v
    mapdrval.s
    mapdrval.o
    dochlss
    syl2anc
    @47
    @36
    simpr
    lspsnel5a
    @48
    cA
    @11
    @35
    cU
    c.0
    mapdrvallem2.z
    mapdrvallem2.a
    @53
    @48
    cA
    cN
    cV
    cU
    @10
    c.0
    mapdrval.v
    mapdrvallem2.n
    mapdrvallem2.z
    mapdrvallem2.a
    @60
    @9
    @17
    @12
    @20
    @36
    simpll2
    lsatlspsn
    @48
    cA
    cU
    cF
    @19
    cH
    cK
    cL
    cO
    cW
    c.0
    mapdrval.h
    mapdrval.o
    mapdrval.u
    mapdrvallem2.z
    mapdrvallem2.a
    mapdrval.f
    mapdrval.l
    @61
    @58
    dochsat0
    lsatcmp2
    mpbid
    eqtr2d
    @48
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    cK
    cO
    cW
    @34
    @1
    mapdrval.h
    @62
    eqid
    #
    mapdrval.o
    @61
    @48
    @55
    @34
    @62
    crn
    #
    wcel
    @47
    @55
    @36
    @18
    cR
    cC
    @19
    @18
    wph
    @56
    @57
    mapdrval.e
    syl
    sselda
    adantr
    @48
    cC
    cU
    vg
    cF
    @19
    cH
    @62
    cK
    cL
    cO
    cW
    mapdrval.h
    @63
    mapdrval.o
    mapdrval.u
    mapdrval.f
    mapdrval.l
    mapdrval.c
    @61
    @58
    lcfl5
    mpbid
    @48
    @4
    @1
    @64
    wcel
    @18
    @4
    @20
    @36
    wph
    @4
    @3
    @8
    @17
    @12
    simp1l2
    ad2antrr
    @48
    cC
    cU
    vg
    cF
    @0
    cH
    @62
    cK
    cL
    cO
    cW
    mapdrval.h
    @63
    mapdrval.o
    mapdrval.u
    mapdrval.f
    mapdrval.l
    mapdrval.c
    @61
    @59
    lcfl5
    mpbid
    doch11
    mpbid
    eqlkr4
    ex
    reximdva
    mpd
    @33
    @25
    vr
    @29
    wrex
    #
    vh
    cR
    wrex
    #
    @30
    @32
    @65
    vh
    cR
    @31
    @25
    vr
    @29
    @0
    @23
    cR
    eleq1
    reximi
    reximi
    @66
    @25
    vh
    cR
    wrex
    #
    vr
    @29
    wrex
    @30
    @25
    vh
    vr
    cR
    @29
    rexcom
    @67
    @27
    vr
    @29
    @25
    vh
    cR
    df-rex
    rexbii
    bitri
    sylib
    syl
    @9
    @17
    @30
    @6
    wi
    @12
    @9
    @27
    @6
    vr
    @29
    @9
    @21
    @29
    wcel
    #
    wa
    #
    @26
    @6
    vh
    @69
    @26
    @6
    @69
    @26
    wa
    #
    @24
    @6
    @70
    cD
    @28
    cT
    @22
    cR
    @29
    cU
    @21
    @19
    @49
    @50
    mapdrval.d
    @51
    mapdrval.t
    @9
    @40
    @68
    @26
    @42
    ad2antrr
    @9
    cR
    cT
    wcel
    #
    @68
    @26
    @5
    @71
    @8
    wph
    @4
    @71
    @3
    mapdrval.r
    3ad2ant1
    #
    adantr
    ad2antrr
    @9
    @68
    @26
    simplr
    @69
    @20
    @25
    simprl
    ldualssvscl
    @25
    @24
    @6
    wi
    @69
    @20
    @6
    @24
    biimpr
    ad2antll
    mpd
    ex
    exlimdv
    rexlimdva
    3ad2ant1
    mpd
    rexlimdv3a
    mpd
    @5
    cD
    clmod
    wcel
    #
    @71
    @7
    wph
    @4
    @73
    @3
    wph
    cD
    cU
    mapdrval.d
    @41
    lduallmod
    3ad2ant1
    @72
    cT
    cR
    cD
    cY
    mapdrvallem2.y
    mapdrval.t
    lss0cl
    syl2anc
    pm2.61ne
    rabssdv
end
