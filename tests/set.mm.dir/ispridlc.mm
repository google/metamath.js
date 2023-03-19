include "ccring.mm"
include "wcel.mm"
include "cpridl.mm"
include "cfv.mm"
include "cidl.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "wss.mm"
include "crngo.mm"
include "wb.mm"
include "crngorngo.mm"
include "ispridl.mm"
include "syl.mm"
include "wa.mm"
include "csn.mm"
include "cigen.mm"
include "snssi.mm"
include "igenidl.mm"
include "syl2an.mm"
include "adantrr.mm"
include "adantrl.mm"
include "wceq.mm"
include "raleq.mm"
include "sseq1.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "orbi2d.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "wrex.mm"
include "crab.mm"
include "cab.mm"
include "prnc.mm"
include "df-rab.mm"
include "syl6eq.mm"
include "abeq2d.mm"
include "anbi12d.mm"
include "adantr.mm"
include "reeanv.mm"
include "anbi2i.mm"
include "an4.mm"
include "bitri.mm"
include "crngm4.mm"
include "3com23.mm"
include "3expa.mm"
include "adantllr.mm"
include "rngocl.mm"
include "syl3an1.mm"
include "3expb.mm"
include "idllmulcl.mm"
include "sylanl1.mm"
include "anassrs.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "adantld.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "ex.mm"
include "igenss.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "ssel.mm"
include "syl5com.mm"
include "orim12d.mm"
include "imim12d.mm"
include "syld.mm"
include "ralrimdvva.mm"
include "adantrd.mm"
include "imdistand.mm"
include "df-3an.mm"
include "3imtr4g.mm"
include "ispridl2.mm"
include "impbid.mm"

theorem ispridlc
  let cP: class P
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vs: setvar s
  assume ispridlc.1: |- G = ( 1st ` R )
  assume ispridlc.2: |- H = ( 2nd ` R )
  assume ispridlc.3: |- X = ran G

  disjoint R a
  disjoint R b
  disjoint a b
  disjoint P a
  disjoint P b
  disjoint X a
  disjoint X b
  disjoint H a
  disjoint H b
  disjoint R x
  disjoint R y
  disjoint R r
  disjoint R s
  disjoint a x
  disjoint a y
  disjoint a r
  disjoint a s
  disjoint b x
  disjoint b y
  disjoint b r
  disjoint b s
  disjoint x y
  disjoint r x
  disjoint s x
  disjoint r y
  disjoint s y
  disjoint r s
  disjoint P x
  disjoint P y
  disjoint P r
  disjoint P s
  disjoint X x
  disjoint X y
  disjoint X r
  disjoint X s
  disjoint G x
  disjoint G y
  disjoint G r
  disjoint G s
  disjoint H x
  disjoint H y
  disjoint H r
  disjoint H s
  assert |- ( R e. CRingOps -> ( P e. ( PrIdl ` R ) <-> ( P e. ( Idl ` R ) /\ P =/= X /\ A. a e. X A. b e. X ( ( a H b ) e. P -> ( a e. P \/ b e. P ) ) ) ) )

  proof
    cR
    ccring
    wcel
    #
    cP
    cR
    cpridl
    cfv
    wcel
    #
    cP
    cR
    cidl
    cfv
    #
    wcel
    #
    cP
    cX
    wne
    #
    va
    cv
    #
    vb
    cv
    #
    cH
    co
    #
    cP
    wcel
    #
    @5
    cP
    wcel
    #
    @6
    cP
    wcel
    #
    wo
    #
    wi
    #
    vb
    cX
    wral
    va
    cX
    wral
    #
    w3a
    #
    @0
    @1
    @3
    @4
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    cP
    wcel
    #
    vy
    vs
    cv
    #
    wral
    #
    vx
    vr
    cv
    #
    wral
    #
    @21
    cP
    wss
    #
    @19
    cP
    wss
    #
    wo
    #
    wi
    #
    vs
    @2
    wral
    vr
    @2
    wral
    #
    w3a
    #
    @14
    @0
    cR
    crngo
    wcel
    #
    @1
    @28
    wb
    cR
    crngorngo
    #
    vx
    vy
    cP
    cR
    cG
    cH
    cX
    vr
    vs
    ispridlc.1
    ispridlc.2
    ispridlc.3
    ispridl
    syl
    @0
    @3
    @4
    wa
    #
    @27
    wa
    @31
    @13
    wa
    @28
    @14
    @0
    @31
    @27
    @13
    @0
    @3
    @27
    @13
    wi
    #
    @4
    @0
    @3
    @32
    @0
    @3
    wa
    #
    @27
    @12
    va
    vb
    cX
    cX
    @33
    @5
    cX
    wcel
    #
    @6
    cX
    wcel
    #
    wa
    #
    wa
    #
    @27
    @18
    vy
    cR
    @6
    csn
    #
    cigen
    co
    #
    wral
    #
    vx
    cR
    @5
    csn
    #
    cigen
    co
    #
    wral
    #
    @42
    cP
    wss
    #
    @39
    cP
    wss
    #
    wo
    #
    wi
    #
    @12
    @0
    @36
    @27
    @47
    wi
    #
    @3
    @0
    @36
    wa
    #
    @42
    @2
    wcel
    #
    @39
    @2
    wcel
    #
    @48
    @0
    @34
    @50
    @35
    @0
    @29
    @41
    cX
    wss
    #
    @50
    @34
    @30
    @5
    cX
    snssi
    #
    cR
    @41
    cG
    cX
    ispridlc.1
    ispridlc.3
    igenidl
    syl2an
    adantrr
    @0
    @35
    @51
    @34
    @0
    @29
    @38
    cX
    wss
    #
    @51
    @35
    @30
    @6
    cX
    snssi
    #
    cR
    @38
    cG
    cX
    ispridlc.1
    ispridlc.3
    igenidl
    syl2an
    adantrl
    @26
    @47
    @20
    vx
    @42
    wral
    #
    @44
    @24
    wo
    #
    wi
    vr
    vs
    @42
    @39
    @2
    @2
    @21
    @42
    wceq
    #
    @22
    @56
    @25
    @57
    @20
    vx
    @21
    @42
    raleq
    @58
    @23
    @44
    @24
    @21
    @42
    cP
    sseq1
    orbi1d
    imbi12d
    @19
    @39
    wceq
    #
    @56
    @43
    @57
    @46
    @59
    @20
    @40
    vx
    @42
    @18
    vy
    @19
    @39
    raleq
    ralbidv
    @59
    @24
    @45
    @44
    @19
    @39
    cP
    sseq1
    orbi2d
    imbi12d
    rspc2v
    syl2anc
    adantlr
    @37
    @8
    @43
    @46
    @11
    @37
    @8
    @43
    @37
    @8
    wa
    #
    @18
    vx
    vy
    @42
    @39
    @60
    @15
    @42
    wcel
    #
    @16
    @39
    wcel
    #
    wa
    #
    @15
    cX
    wcel
    #
    @15
    @21
    @5
    cH
    co
    #
    wceq
    #
    vr
    cX
    wrex
    #
    wa
    #
    @16
    cX
    wcel
    #
    @16
    @19
    @6
    cH
    co
    #
    wceq
    #
    vs
    cX
    wrex
    #
    wa
    #
    wa
    #
    @18
    @37
    @63
    @74
    wb
    #
    @8
    @0
    @36
    @75
    @3
    @49
    @61
    @68
    @62
    @73
    @0
    @34
    @61
    @68
    wb
    @35
    @0
    @34
    wa
    #
    @68
    vx
    @42
    @76
    @42
    @67
    vx
    cX
    crab
    @68
    vx
    cab
    vx
    vr
    @5
    cR
    cG
    cH
    cX
    ispridlc.1
    ispridlc.2
    ispridlc.3
    prnc
    @67
    vx
    cX
    df-rab
    syl6eq
    abeq2d
    adantrr
    @0
    @35
    @62
    @73
    wb
    @34
    @0
    @35
    wa
    #
    @73
    vy
    @39
    @77
    @39
    @72
    vy
    cX
    crab
    @73
    vy
    cab
    vy
    vs
    @6
    cR
    cG
    cH
    cX
    ispridlc.1
    ispridlc.2
    ispridlc.3
    prnc
    @72
    vy
    cX
    df-rab
    syl6eq
    abeq2d
    adantrl
    anbi12d
    adantlr
    adantr
    @74
    @64
    @69
    wa
    #
    @66
    @71
    wa
    #
    vs
    cX
    wrex
    vr
    cX
    wrex
    #
    wa
    #
    @60
    @18
    @81
    @78
    @67
    @72
    wa
    #
    wa
    @74
    @80
    @82
    @78
    @66
    @71
    vr
    vs
    cX
    cX
    reeanv
    anbi2i
    @64
    @69
    @67
    @72
    an4
    bitri
    @60
    @80
    @18
    @78
    @60
    @79
    @18
    vr
    vs
    cX
    cX
    @60
    @21
    cX
    wcel
    #
    @19
    cX
    wcel
    #
    wa
    #
    wa
    #
    @18
    @79
    @65
    @70
    cH
    co
    #
    cP
    wcel
    @86
    @21
    @19
    cH
    co
    #
    @7
    cH
    co
    #
    @87
    cP
    @37
    @85
    @89
    @87
    wceq
    #
    @8
    @0
    @36
    @85
    @90
    @3
    @0
    @36
    @85
    @90
    @0
    @85
    @36
    @90
    @21
    @19
    @5
    @6
    cR
    cG
    cH
    cX
    ispridlc.1
    ispridlc.2
    ispridlc.3
    crngm4
    3com23
    3expa
    adantllr
    adantlr
    @33
    @8
    @85
    @89
    cP
    wcel
    #
    @36
    @33
    @8
    wa
    @85
    @88
    cX
    wcel
    #
    @91
    @33
    @85
    @92
    @8
    @0
    @85
    @92
    @3
    @0
    @83
    @84
    @92
    @0
    @29
    @83
    @84
    @92
    @30
    @21
    @19
    cR
    cG
    cH
    cX
    ispridlc.1
    ispridlc.2
    ispridlc.3
    rngocl
    syl3an1
    3expb
    adantlr
    adantlr
    @33
    @8
    @92
    @91
    @0
    @29
    @3
    @8
    @92
    wa
    @91
    @30
    @7
    @88
    cR
    cG
    cH
    cP
    cX
    ispridlc.1
    ispridlc.2
    ispridlc.3
    idllmulcl
    sylanl1
    anassrs
    syldan
    adantllr
    eqeltrrd
    @79
    @17
    @87
    cP
    @15
    @65
    @16
    @70
    cH
    oveq12
    eleq1d
    syl5ibrcom
    rexlimdvva
    adantld
    syl5bir
    sylbid
    ralrimivv
    ex
    @0
    @36
    @46
    @11
    wi
    @3
    @49
    @44
    @9
    @45
    @10
    @49
    @5
    @42
    wcel
    #
    @44
    @9
    @0
    @34
    @93
    @35
    @76
    @41
    @42
    wss
    #
    @93
    @0
    @29
    @52
    @94
    @34
    @30
    @53
    cR
    @41
    cG
    cX
    ispridlc.1
    ispridlc.3
    igenss
    syl2an
    @5
    @42
    va
    vex
    snss
    sylibr
    adantrr
    @42
    cP
    @5
    ssel
    syl5com
    @49
    @6
    @39
    wcel
    #
    @45
    @10
    @0
    @35
    @95
    @34
    @77
    @38
    @39
    wss
    #
    @95
    @0
    @29
    @54
    @96
    @35
    @30
    @55
    cR
    @38
    cG
    cX
    ispridlc.1
    ispridlc.3
    igenss
    syl2an
    @6
    @39
    vb
    vex
    snss
    sylibr
    adantrl
    @39
    cP
    @6
    ssel
    syl5com
    orim12d
    adantlr
    imim12d
    syld
    ralrimdvva
    ex
    adantrd
    imdistand
    @3
    @4
    @27
    df-3an
    @3
    @4
    @13
    df-3an
    3imtr4g
    sylbid
    @0
    @29
    @14
    @1
    wi
    @30
    @29
    @14
    @1
    cP
    cR
    cG
    cH
    cX
    va
    vb
    ispridlc.1
    ispridlc.2
    ispridlc.3
    ispridl2
    ex
    syl
    impbid
end
