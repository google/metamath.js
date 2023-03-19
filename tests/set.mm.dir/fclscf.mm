include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cfcls.mm"
include "co.mm"
include "cfil.mm"
include "wral.mm"
include "simpll.mm"
include "simplr.mm"
include "wb.mm"
include "fclstopon.mm"
include "ad2antll.mm"
include "mpbid.mm"
include "simprl.mm"
include "fclsss1.mm"
include "syl3anc.mm"
include "simprr.mm"
include "sseldd.mm"
include "expr.mm"
include "ssrdv.mm"
include "ralrimivw.mm"
include "wrex.mm"
include "wi.mm"
include "wceq.mm"
include "simpllr.mm"
include "toponmax.mm"
include "ssid.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpanr2.mm"
include "ex.mm"
include "3syl.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "cdif.mm"
include "cpw.mm"
include "crab.mm"
include "wn.mm"
include "simplll.mm"
include "simprrr.mm"
include "supnfcls.mm"
include "syl.mm"
include "difssd.mm"
include "toponss.mm"
include "syl2anc.mm"
include "simprrl.mm"
include "pssdifn0.mm"
include "supfil.mm"
include "fclsopn.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "sseld.mm"
include "sylbird.mm"
include "mtod.mm"
include "rexanali.mm"
include "rexnal.mm"
include "elrab.mm"
include "simprbi.mm"
include "sslin.mm"
include "ssn0.mm"
include "necon1bd.mm"
include "inssdif0.mm"
include "syl6ibr.mm"
include "sylan.mm"
include "df-ss.mm"
include "sylib.mm"
include "sseq1d.mm"
include "biimpd.mm"
include "syl9r.mm"
include "syl5.mm"
include "rexlimdv.mm"
include "syl5bir.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"
include "anassrs.mm"
include "exp32.mm"
include "pm2.61dne.mm"
include "ralrimiv.mm"
include "ctop.mm"
include "topontop.mm"
include "eltop2.mm"
include "mpbird.mm"
include "impbida.mm"

theorem fclscf
  let vf: setvar f
  let cJ: class J
  let cK: class K
  let cX: class X
  let vn: setvar n
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y

  disjoint J f
  disjoint K f
  disjoint X f
  disjoint f n
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint J n
  disjoint u x
  disjoint u y
  disjoint J u
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K n
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint X n
  disjoint X u
  disjoint X x
  disjoint X y
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` X ) ) -> ( J C_ K <-> A. f e. ( Fil ` X ) ( K fClus f ) C_ ( J fClus f ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cK
    @0
    wcel
    #
    wa
    #
    cJ
    cK
    wss
    #
    cK
    vf
    cv
    #
    cfcls
    co
    #
    cJ
    @5
    cfcls
    co
    #
    wss
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    @3
    @4
    wa
    #
    @8
    vf
    @9
    @11
    vx
    @6
    @7
    @3
    @4
    vx
    cv
    #
    @6
    wcel
    #
    @12
    @7
    wcel
    @3
    @4
    @13
    wa
    #
    wa
    #
    @6
    @7
    @12
    @15
    @1
    @5
    @9
    wcel
    #
    @4
    @8
    @1
    @2
    @14
    simpll
    @15
    @2
    @16
    @1
    @2
    @14
    simplr
    @13
    @2
    @16
    wb
    @3
    @4
    @12
    @5
    cK
    cX
    fclstopon
    ad2antll
    mpbid
    @3
    @4
    @13
    simprl
    @5
    cJ
    cK
    cX
    fclsss1
    syl3anc
    @3
    @4
    @13
    simprr
    sseldd
    expr
    ssrdv
    ralrimivw
    @3
    @10
    wa
    #
    vx
    cJ
    cK
    @17
    @12
    cJ
    wcel
    #
    @12
    cK
    wcel
    #
    @17
    @18
    wa
    #
    @19
    vy
    cv
    #
    vu
    cv
    #
    wcel
    #
    @22
    @12
    wss
    #
    wa
    #
    vu
    cK
    wrex
    #
    vy
    @12
    wral
    #
    @20
    @26
    vy
    @12
    @20
    @21
    @12
    wcel
    #
    @26
    wi
    #
    @12
    cX
    @20
    @29
    @12
    cX
    wceq
    #
    @21
    cX
    wcel
    #
    @23
    @22
    cX
    wss
    #
    wa
    #
    vu
    cK
    wrex
    #
    wi
    #
    @20
    @2
    cX
    cK
    wcel
    #
    @35
    @1
    @2
    @10
    @18
    simpllr
    #
    cX
    cK
    toponmax
    @36
    @31
    @34
    @36
    @31
    cX
    cX
    wss
    #
    @34
    cX
    ssid
    @33
    @31
    @38
    wa
    vu
    cX
    cK
    @22
    cX
    wceq
    @23
    @31
    @32
    @38
    @22
    cX
    @21
    eleq2
    @22
    cX
    cX
    sseq1
    anbi12d
    rspcev
    mpanr2
    ex
    3syl
    @30
    @28
    @31
    @26
    @34
    @12
    cX
    @21
    eleq2
    @30
    @25
    @33
    vu
    cK
    @30
    @24
    @32
    @23
    @12
    cX
    @22
    sseq2
    anbi2d
    rexbidv
    imbi12d
    syl5ibrcom
    @20
    @12
    cX
    wne
    #
    @28
    @26
    @17
    @18
    @39
    @28
    wa
    #
    @26
    @17
    @18
    @40
    wa
    #
    wa
    #
    @23
    @22
    vn
    cv
    #
    cin
    #
    c0
    wne
    #
    vn
    cX
    @12
    cdif
    #
    @21
    wss
    #
    vy
    cX
    cpw
    #
    crab
    #
    wral
    #
    wi
    vu
    cK
    wral
    #
    wn
    #
    @26
    @42
    @51
    @21
    cJ
    @49
    cfcls
    co
    #
    wcel
    #
    @42
    @1
    @18
    @28
    @54
    wn
    @1
    @2
    @10
    @41
    simplll
    #
    @17
    @18
    @40
    simprl
    #
    @17
    @18
    @39
    @28
    simprrr
    #
    vy
    @21
    @12
    cJ
    cX
    supnfcls
    syl3anc
    @42
    @51
    @21
    cK
    @49
    cfcls
    co
    #
    wcel
    #
    @54
    @42
    @59
    @31
    @51
    wa
    #
    @51
    @42
    @2
    @49
    @9
    wcel
    #
    @59
    @60
    wb
    @1
    @2
    @10
    @41
    simpllr
    #
    @42
    cX
    cJ
    wcel
    #
    @46
    cX
    wss
    @46
    c0
    wne
    #
    @61
    @42
    @1
    @63
    @55
    cX
    cJ
    toponmax
    syl
    @42
    cX
    @12
    difssd
    @42
    @12
    cX
    wss
    #
    @39
    @64
    @42
    @1
    @18
    @65
    @55
    @56
    @12
    cJ
    cX
    toponss
    syl2anc
    #
    @17
    @18
    @39
    @28
    simprrl
    @12
    cX
    pssdifn0
    syl2anc
    vy
    cX
    @46
    cJ
    supfil
    syl3anc
    #
    @21
    vu
    @49
    cK
    cX
    vn
    fclsopn
    syl2anc
    @42
    @31
    @51
    @42
    @12
    cX
    @21
    @66
    @57
    sseldd
    biantrurd
    bitr4d
    @42
    @58
    @53
    @21
    @42
    @61
    @10
    @58
    @53
    wss
    #
    @67
    @3
    @10
    @41
    simplr
    @8
    @68
    vf
    @49
    @9
    @5
    @49
    wceq
    @6
    @58
    @7
    @53
    @5
    @49
    cK
    cfcls
    oveq2
    @5
    @49
    cJ
    cfcls
    oveq2
    sseq12d
    rspcv
    sylc
    sseld
    sylbird
    mtod
    @52
    @23
    @50
    wn
    #
    wa
    #
    vu
    cK
    wrex
    @42
    @26
    @23
    @50
    vu
    cK
    rexanali
    @42
    @70
    @25
    vu
    cK
    @42
    @22
    cK
    wcel
    #
    wa
    #
    @69
    @24
    @23
    @69
    @45
    wn
    #
    vn
    @49
    wrex
    @72
    @24
    @45
    vn
    @49
    rexnal
    @72
    @73
    @24
    vn
    @49
    @43
    @49
    wcel
    #
    @22
    @46
    cin
    #
    @44
    wss
    #
    @72
    @73
    @24
    wi
    @74
    @46
    @43
    wss
    #
    @76
    @74
    @43
    @48
    wcel
    @77
    @47
    @77
    vy
    @43
    @48
    @21
    @43
    @46
    sseq2
    elrab
    simprbi
    @46
    @43
    @22
    sslin
    syl
    @76
    @73
    @22
    cX
    cin
    #
    @12
    wss
    #
    @72
    @24
    @76
    @73
    @75
    c0
    wceq
    @79
    @76
    @45
    @75
    c0
    @76
    @75
    c0
    wne
    @45
    @75
    @44
    ssn0
    ex
    necon1bd
    @22
    cX
    @12
    inssdif0
    syl6ibr
    @72
    @79
    @24
    @72
    @78
    @22
    @12
    @72
    @32
    @78
    @22
    wceq
    @42
    @2
    @71
    @32
    @62
    @22
    cK
    cX
    toponss
    sylan
    @22
    cX
    df-ss
    sylib
    sseq1d
    biimpd
    syl9r
    syl5
    rexlimdv
    syl5bir
    anim2d
    reximdva
    syl5bir
    mpd
    anassrs
    exp32
    pm2.61dne
    ralrimiv
    @20
    @2
    cK
    ctop
    wcel
    @19
    @27
    wb
    @37
    cX
    cK
    topontop
    vy
    vu
    @12
    cK
    eltop2
    3syl
    mpbird
    ex
    ssrdv
    impbida
end
