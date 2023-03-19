include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cs3.mm"
include "csn.mm"
include "cnbgr.mm"
include "co.mm"
include "cdif.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "c2.mm"
include "cwwspthsn.mm"
include "c1.mm"
include "wceq.mm"
include "wb.mm"
include "fusgreg2wsplem.mm"
include "adantl.mm"
include "wne.mm"
include "cpr.mm"
include "cedg.mm"
include "cwwspthsnon.mm"
include "wspthsnwspthsnon.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "adantr.mm"
include "eqid.mm"
include "usgr2wspthon.mm"
include "sylan.mm"
include "2rexbidva.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "wex.mm"
include "19.41vv.mm"
include "wn.mm"
include "velsn.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "a1i.mm"
include "simplr.mm"
include "anass.mm"
include "ancom.mm"
include "an12.mm"
include "nesym.mm"
include "prcom.mm"
include "eleq1i.mm"
include "anbi12ci.mm"
include "bitri.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "preq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "s3eq2.mm"
include "eqeq2d.mm"
include "wi.mm"
include "fveq1.mm"
include "cvv.mm"
include "vex.mm"
include "s3fv1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "com12.mm"
include "ad2antll.mm"
include "imp.mm"
include "rspcebdv.mm"
include "pm5.32da.mm"
include "an32.mm"
include "cumgr.mm"
include "usgrumgr.mm"
include "umgrpredgv.mm"
include "simpld.mm"
include "ex.mm"
include "expcom.mm"
include "anim12d.mm"
include "3syl.mm"
include "impcom.mm"
include "sylan9eqr.mm"
include "jca.mm"
include "pm4.71rd.mm"
include "3bitr4d.mm"
include "nbusgreledg.mm"
include "syl.mm"
include "eldif.mm"
include "notbid.mm"
include "2exbidv.mm"
include "syl5bbr.mm"
include "r2ex.mm"
include "3bitr4g.mm"
include "eleq1w.mm"
include "2rexbidv.mm"
include "elab.mm"
include "3bitrd.mm"
include "bitrd.mm"
include "eqrdv.mm"
include "dfiunv2.mm"
include "syl6eqr.mm"

theorem fusgr2wsp2nb
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vz: setvar z
  let vp: setvar p
  assume frgrhash2wsp.v: |- V = ( Vtx ` G )
  assume fusgreg2wsp.m: |- M = ( a e. V |-> { w e. ( 2 WSPathsN G ) | ( w ` 1 ) = a } )

  disjoint G a
  disjoint V a
  disjoint G w
  disjoint N a
  disjoint N w
  disjoint a w
  disjoint G x
  disjoint G y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint V x
  disjoint V y
  disjoint G b
  disjoint a b
  disjoint V b
  disjoint G m
  disjoint G z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint x z
  disjoint y z
  disjoint G p
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint M z
  disjoint N m
  disjoint N z
  disjoint N p
  disjoint V m
  disjoint V z
  disjoint w z
  assert |- ( ( G e. FinUSGraph /\ N e. V ) -> ( M ` N ) = U_ x e. ( G NeighbVtx N ) U_ y e. ( ( G NeighbVtx N ) \ { x } ) { <" x N y "> } )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cN
    cM
    cfv
    #
    vp
    cv
    #
    vx
    cv
    #
    cN
    vy
    cv
    #
    cs3
    #
    csn
    #
    wcel
    #
    vy
    cG
    cN
    cnbgr
    co
    #
    @5
    csn
    #
    cdif
    #
    wrex
    vx
    @10
    wrex
    #
    vp
    cab
    #
    vx
    @10
    vy
    @12
    @8
    ciun
    ciun
    @2
    vz
    @3
    @14
    @2
    vz
    cv
    #
    @3
    wcel
    #
    @15
    c2
    cG
    cwwspthsn
    co
    wcel
    #
    c1
    @15
    cfv
    #
    cN
    wceq
    #
    wa
    #
    @15
    @14
    wcel
    #
    @1
    @16
    @20
    wb
    @0
    vw
    cG
    cM
    cN
    cV
    vz
    va
    frgrhash2wsp.v
    fusgreg2wsp.m
    fusgreg2wsplem
    adantl
    @2
    @20
    @15
    @5
    vm
    cv
    #
    @6
    cs3
    #
    wceq
    #
    @5
    @6
    wne
    #
    wa
    #
    @5
    @22
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    @22
    @6
    cpr
    #
    @28
    wcel
    #
    wa
    #
    wa
    #
    vm
    cV
    wrex
    #
    vy
    cV
    wrex
    vx
    cV
    wrex
    #
    @19
    wa
    #
    @15
    @8
    wcel
    #
    vy
    @12
    wrex
    vx
    @10
    wrex
    #
    @21
    @2
    @17
    @35
    @19
    @17
    @15
    @5
    @6
    c2
    cG
    cwwspthsnon
    co
    co
    wcel
    #
    vy
    cV
    wrex
    vx
    cV
    wrex
    @2
    @35
    cG
    c2
    cV
    @15
    vx
    vy
    frgrhash2wsp.v
    wspthsnwspthsnon
    @2
    @39
    @34
    vx
    vy
    cV
    cV
    @2
    cG
    cusgr
    wcel
    #
    @5
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    wa
    #
    @39
    @34
    wb
    @0
    @40
    @1
    cG
    fusgrusgr
    #
    adantr
    @5
    @6
    @15
    @28
    cG
    cV
    vm
    frgrhash2wsp.v
    @28
    eqid
    #
    usgr2wspthon
    sylan
    2rexbidva
    syl5bb
    anbi1d
    @2
    @43
    @34
    wa
    #
    vy
    wex
    vx
    wex
    #
    @19
    wa
    #
    @5
    @10
    wcel
    #
    @6
    @12
    wcel
    #
    wa
    #
    @37
    wa
    #
    vy
    wex
    vx
    wex
    #
    @36
    @38
    @48
    @46
    @19
    wa
    #
    vy
    wex
    vx
    wex
    @2
    @53
    @46
    @19
    vx
    vy
    19.41vv
    @2
    @54
    @52
    vx
    vy
    @2
    @5
    cN
    cpr
    #
    @28
    wcel
    #
    @6
    cN
    cpr
    #
    @28
    wcel
    #
    @6
    @5
    wceq
    #
    wn
    #
    wa
    #
    wa
    #
    @15
    @7
    wceq
    #
    wa
    #
    @62
    @37
    wa
    #
    @54
    @52
    @64
    @65
    wb
    @2
    @63
    @37
    @62
    @37
    @63
    vz
    @7
    velsn
    bicomi
    anbi2i
    a1i
    @2
    @43
    @19
    wa
    #
    @34
    wa
    #
    @66
    @64
    wa
    @54
    @64
    @2
    @66
    @34
    @64
    @2
    @66
    wa
    #
    @33
    @64
    vm
    cN
    cV
    @0
    @1
    @66
    simplr
    @22
    cN
    wceq
    #
    @33
    @64
    wb
    @68
    @33
    @29
    @6
    @22
    cpr
    #
    @28
    wcel
    #
    @60
    wa
    #
    wa
    #
    @24
    wa
    #
    @69
    @64
    @33
    @24
    @25
    @32
    wa
    #
    wa
    @75
    @24
    wa
    @74
    @24
    @25
    @32
    anass
    @24
    @75
    ancom
    @75
    @73
    @24
    @75
    @29
    @25
    @31
    wa
    #
    wa
    @73
    @25
    @29
    @31
    an12
    @76
    @72
    @29
    @25
    @60
    @31
    @71
    @5
    @6
    nesym
    @30
    @70
    @28
    @22
    @6
    prcom
    eleq1i
    anbi12ci
    anbi2i
    bitri
    anbi1i
    3bitri
    @69
    @73
    @62
    @24
    @63
    @69
    @29
    @56
    @72
    @61
    @69
    @27
    @55
    @28
    @22
    cN
    @5
    preq2
    eleq1d
    @69
    @71
    @58
    @60
    @69
    @70
    @57
    @28
    @22
    cN
    @6
    preq2
    eleq1d
    anbi1d
    anbi12d
    @69
    @23
    @7
    @15
    @5
    @22
    @6
    cN
    s3eq2
    eqeq2d
    anbi12d
    syl5bb
    adantl
    @68
    @33
    @69
    @19
    @33
    @69
    wi
    @2
    @43
    @33
    @19
    @69
    @26
    @19
    @69
    wi
    #
    @32
    @24
    @77
    @25
    @24
    @19
    @69
    @24
    @18
    @22
    cN
    @24
    @18
    c1
    @23
    cfv
    #
    @22
    c1
    @15
    @23
    fveq1
    @22
    cvv
    wcel
    @78
    @22
    wceq
    vm
    vex
    @5
    @22
    @6
    cvv
    s3fv1
    ax-mp
    syl6eq
    eqeq1d
    biimpd
    adantr
    adantr
    com12
    ad2antll
    imp
    rspcebdv
    pm5.32da
    @54
    @67
    wb
    @2
    @43
    @34
    @19
    an32
    a1i
    @2
    @64
    @66
    @2
    @64
    @66
    @2
    @64
    wa
    @43
    @19
    @64
    @2
    @43
    @62
    @2
    @43
    wi
    @63
    @2
    @62
    @43
    @0
    @62
    @43
    wi
    #
    @1
    @0
    @40
    cG
    cumgr
    wcel
    #
    @79
    @44
    cG
    usgrumgr
    @80
    @56
    @41
    @61
    @42
    @80
    @56
    @41
    @80
    @56
    wa
    @41
    @1
    @28
    cG
    @5
    cN
    cV
    frgrhash2wsp.v
    @45
    umgrpredgv
    simpld
    ex
    @61
    @80
    @42
    @58
    @80
    @42
    wi
    @60
    @80
    @58
    @42
    @80
    @58
    wa
    @42
    @1
    @28
    cG
    @6
    cN
    cV
    frgrhash2wsp.v
    @45
    umgrpredgv
    simpld
    expcom
    adantr
    com12
    anim12d
    3syl
    adantr
    com12
    adantr
    impcom
    @64
    @2
    @18
    c1
    @7
    cfv
    #
    cN
    @63
    @18
    @81
    wceq
    @62
    c1
    @15
    @7
    fveq1
    adantl
    @1
    @81
    cN
    wceq
    @0
    @5
    cN
    @6
    cV
    s3fv1
    adantl
    sylan9eqr
    jca
    ex
    pm4.71rd
    3bitr4d
    @2
    @51
    @62
    @37
    @2
    @49
    @56
    @50
    @61
    @0
    @49
    @56
    wb
    #
    @1
    @0
    @40
    @82
    @44
    @28
    cG
    cN
    @5
    @45
    nbusgreledg
    syl
    adantr
    @50
    @6
    @10
    wcel
    #
    @6
    @11
    wcel
    #
    wn
    #
    wa
    @2
    @61
    @6
    @10
    @11
    eldif
    @2
    @83
    @58
    @85
    @60
    @0
    @83
    @58
    wb
    #
    @1
    @0
    @40
    @86
    @44
    @28
    cG
    cN
    @6
    @45
    nbusgreledg
    syl
    adantr
    @2
    @84
    @59
    @84
    @59
    wb
    @2
    vy
    @5
    velsn
    a1i
    notbid
    anbi12d
    syl5bb
    anbi12d
    anbi1d
    3bitr4d
    2exbidv
    syl5bbr
    @35
    @47
    @19
    @34
    vx
    vy
    cV
    cV
    r2ex
    anbi1i
    @37
    vx
    vy
    @10
    @12
    r2ex
    3bitr4g
    @38
    @21
    wb
    @2
    @21
    @38
    @13
    @38
    vp
    @15
    vz
    vex
    @4
    @15
    wceq
    @9
    @37
    vx
    vy
    @10
    @12
    vp
    vz
    @8
    eleq1w
    2rexbidv
    elab
    bicomi
    a1i
    3bitrd
    bitrd
    eqrdv
    vx
    vy
    vp
    @10
    @12
    @8
    dfiunv2
    syl6eqr
end
