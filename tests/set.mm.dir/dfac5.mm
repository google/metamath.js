include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "weu.mm"
include "wex.mm"
include "wal.mm"
include "wfn.mm"
include "cfv.mm"
include "dfac4.mm"
include "crn.mm"
include "neeq1.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "r19.26.mm"
include "bitr4i.mm"
include "pm3.35.mm"
include "ancoms.mm"
include "ralimi.mm"
include "sylbi.mm"
include "wel.mm"
include "wb.mm"
include "elin.mm"
include "wrex.mm"
include "fvelrnb.mm"
include "biimpac.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "neeq2.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "eleq1.mm"
include "biimpar.mm"
include "wn.mm"
include "minel.mm"
include "ex.mm"
include "imim2d.mm"
include "imp.mm"
include "necon4ad.mm"
include "sylan2.mm"
include "eqeq2.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "syl5ib.mm"
include "ad2antrl.mm"
include "mpd.mm"
include "exp32.mm"
include "syl6com.mm"
include "com14.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "expd.mm"
include "com4t.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "adantlr.mm"
include "fnfvelrn.mm"
include "expcom.mm"
include "anim12d.mm"
include "syl6ibr.mm"
include "com13.mm"
include "imp31.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "impbid.mm"
include "alrimdv.mm"
include "fvex.mm"
include "bibi2d.mm"
include "albidv.mm"
include "spcev.mm"
include "df-eu.mm"
include "sylibr.mm"
include "syl6.mm"
include "ralimdva.mm"
include "vex.mm"
include "rnex.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "ralbidv.mm"
include "exlimiv.mm"
include "alimi.mm"
include "csn.mm"
include "cxp.mm"
include "cab.mm"
include "cuni.mm"
include "eqid.mm"
include "biid.mm"
include "dfac5lem5.mm"
include "alrimiv.mm"
include "dfac3.mm"
include "impbii.mm"

theorem dfac5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vh: setvar h
  let vu: setvar u
  let vt: setvar t

  disjoint x z
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w z
  disjoint v z
  disjoint w y
  disjoint v y
  disjoint v w
  disjoint f x
  disjoint f z
  disjoint f y
  disjoint f w
  disjoint f v
  disjoint f h
  disjoint f u
  disjoint f t
  disjoint h x
  disjoint u x
  disjoint t x
  disjoint h z
  disjoint u z
  disjoint t z
  disjoint h y
  disjoint u y
  disjoint t y
  disjoint h w
  disjoint u w
  disjoint t w
  disjoint h v
  disjoint u v
  disjoint t v
  disjoint h u
  disjoint h t
  disjoint t u
  assert |- ( CHOICE <-> A. x ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) -> E. y A. z e. x E! v v e. ( z i^i y ) ) )

  proof
    wac
    vz
    cv
    #
    c0
    wne
    #
    vz
    vx
    cv
    #
    wral
    #
    @0
    vw
    cv
    #
    wne
    #
    @0
    @4
    cin
    #
    c0
    wceq
    #
    wi
    #
    vw
    @2
    wral
    #
    vz
    @2
    wral
    #
    wa
    #
    vv
    cv
    #
    @0
    vy
    cv
    #
    cin
    #
    wcel
    #
    vv
    weu
    #
    vz
    @2
    wral
    #
    vy
    wex
    #
    wi
    #
    vx
    wal
    #
    wac
    vf
    cv
    #
    @2
    wfn
    #
    @4
    c0
    wne
    #
    @4
    @21
    cfv
    #
    @4
    wcel
    #
    wi
    #
    vw
    @2
    wral
    #
    wa
    #
    vf
    wex
    #
    vx
    wal
    @20
    vx
    vw
    vf
    dfac4
    @29
    @19
    vx
    @28
    @19
    vf
    @28
    @11
    @12
    @0
    @21
    crn
    #
    cin
    #
    wcel
    #
    vv
    weu
    #
    vz
    @2
    wral
    #
    @18
    @22
    @27
    @3
    @10
    @34
    @22
    @27
    @3
    @10
    @34
    wi
    #
    @27
    @3
    wa
    #
    @25
    vw
    @2
    wral
    #
    @22
    @35
    @36
    @26
    @23
    wa
    #
    vw
    @2
    wral
    #
    @37
    @36
    @27
    @23
    vw
    @2
    wral
    #
    wa
    @39
    @3
    @40
    @27
    @1
    @23
    vz
    vw
    @2
    @0
    @4
    c0
    neeq1
    cbvralv
    anbi2i
    @26
    @23
    vw
    @2
    r19.26
    bitr4i
    @38
    @25
    vw
    @2
    @23
    @26
    @25
    @23
    @25
    pm3.35
    ancoms
    ralimi
    sylbi
    @22
    @37
    @35
    @22
    @37
    wa
    #
    @9
    @33
    vz
    @2
    @41
    vz
    vx
    wel
    #
    wa
    #
    @9
    @32
    @12
    @0
    @21
    cfv
    #
    wceq
    #
    wb
    #
    vv
    wal
    #
    @33
    @43
    @9
    @46
    vv
    @43
    @9
    @46
    @43
    @9
    wa
    @32
    @45
    @41
    @9
    @32
    @45
    wi
    #
    @42
    @22
    @37
    @9
    @48
    @37
    @9
    wa
    @22
    @25
    @8
    wa
    #
    vw
    @2
    wral
    #
    @48
    @25
    @8
    vw
    @2
    r19.26
    @32
    vv
    vz
    wel
    #
    @12
    @30
    wcel
    #
    wa
    @22
    @50
    wa
    @45
    @12
    @0
    @30
    elin
    @22
    @50
    @51
    @52
    @45
    @51
    @52
    @22
    @50
    @45
    @51
    @52
    @22
    @50
    @45
    wi
    #
    @52
    @22
    wa
    vt
    cv
    #
    @21
    cfv
    #
    @12
    wceq
    #
    vt
    @2
    wrex
    #
    @51
    @53
    @22
    @52
    @57
    vt
    @2
    @12
    @21
    fvelrnb
    biimpac
    @51
    @56
    @53
    vt
    @2
    @50
    vt
    vx
    wel
    #
    @56
    @51
    @45
    @58
    @50
    @55
    @54
    wcel
    #
    @0
    @54
    wne
    #
    @0
    @54
    cin
    #
    c0
    wceq
    #
    wi
    #
    wa
    #
    @56
    @51
    @45
    wi
    wi
    @49
    @64
    vw
    @54
    @2
    vw
    vt
    weq
    #
    @25
    @59
    @8
    @63
    @65
    @24
    @55
    @4
    @54
    @4
    @54
    @21
    fveq2
    @65
    id
    eleq12d
    @65
    @5
    @60
    @7
    @62
    @4
    @54
    @0
    neeq2
    @65
    @6
    @61
    c0
    @4
    @54
    @0
    ineq2
    eqeq1d
    imbi12d
    anbi12d
    rspcv
    @64
    @56
    @51
    @45
    @64
    @56
    @51
    wa
    #
    wa
    vz
    vt
    weq
    #
    @45
    @66
    @64
    @55
    @0
    wcel
    #
    @67
    @56
    @68
    @51
    @55
    @12
    @0
    eleq1
    biimpar
    @64
    @68
    @67
    @64
    @68
    @0
    @54
    @59
    @63
    @60
    @68
    wn
    #
    wi
    @59
    @62
    @69
    @60
    @59
    @62
    @69
    @55
    @54
    @0
    minel
    ex
    imim2d
    imp
    necon4ad
    imp
    sylan2
    @56
    @67
    @45
    wi
    @64
    @51
    @67
    @44
    @55
    wceq
    #
    @56
    @45
    @0
    @54
    @21
    fveq2
    @56
    @70
    @44
    @12
    wceq
    @45
    @55
    @12
    @44
    eqeq2
    @44
    @12
    eqcom
    syl6bb
    syl5ib
    ad2antrl
    mpd
    exp32
    syl6com
    com14
    rexlimdv
    syl5
    expd
    com4t
    imp4b
    syl5bi
    sylan2br
    anassrs
    adantlr
    @43
    @45
    @32
    wi
    @9
    @43
    @32
    @45
    @44
    @31
    wcel
    #
    @22
    @37
    @42
    @71
    @42
    @37
    @22
    @71
    @42
    @37
    @22
    @71
    @42
    @37
    @22
    wa
    @44
    @0
    wcel
    #
    @44
    @30
    wcel
    #
    wa
    @71
    @42
    @37
    @72
    @22
    @73
    @25
    @72
    vw
    @0
    @2
    vw
    vz
    weq
    #
    @24
    @44
    @4
    @0
    @4
    @0
    @21
    fveq2
    @74
    id
    eleq12d
    rspcv
    @22
    @42
    @73
    @2
    @0
    @21
    fnfvelrn
    expcom
    anim12d
    @44
    @0
    @30
    elin
    syl6ibr
    expd
    com13
    imp31
    @12
    @44
    @31
    eleq1
    syl5ibrcom
    adantr
    impbid
    ex
    alrimdv
    @47
    @32
    vv
    vh
    weq
    #
    wb
    #
    vv
    wal
    #
    vh
    wex
    @33
    @77
    @47
    vh
    @44
    @0
    @21
    fvex
    vh
    cv
    #
    @44
    wceq
    #
    @76
    @46
    vv
    @79
    @75
    @45
    @32
    @78
    @44
    @12
    eqeq2
    bibi2d
    albidv
    spcev
    @32
    vv
    vh
    df-eu
    sylibr
    syl6
    ralimdva
    ex
    syl5
    expd
    imp4b
    @17
    @34
    vy
    @30
    @21
    vf
    vex
    rnex
    @13
    @30
    wceq
    #
    @16
    @33
    vz
    @2
    @80
    @15
    @32
    vv
    @80
    @14
    @31
    @12
    @13
    @30
    @0
    ineq2
    eleq2d
    eubidv
    ralbidv
    spcev
    syl6
    exlimiv
    alimi
    sylbi
    @20
    @26
    vw
    @78
    wral
    vf
    wex
    #
    vh
    wal
    wac
    @20
    @81
    vh
    @20
    vx
    vy
    vz
    vw
    vv
    vu
    vt
    vu
    cv
    #
    c0
    wne
    @82
    @54
    csn
    @54
    cxp
    wceq
    vt
    @78
    wrex
    wa
    vu
    cab
    #
    @83
    cuni
    @13
    cin
    #
    vf
    vh
    @83
    eqid
    @84
    eqid
    @20
    biid
    dfac5lem5
    alrimiv
    vh
    vw
    vf
    dfac3
    sylibr
    impbii
end
