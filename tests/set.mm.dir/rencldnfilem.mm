include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cfn.mm"
include "wi.mm"
include "wceq.mm"
include "crab.mm"
include "ccnv.mm"
include "csup.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simp-4l.mm"
include "simpr.mm"
include "sseldd.mm"
include "recnd.mm"
include "simp-4r.mm"
include "subcld.mm"
include "cc0.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "nelneq.mm"
include "syl2anc.mm"
include "cc.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "absrpcld.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "adantr.mm"
include "cab.mm"
include "abrexfi.mm"
include "rabssab.mm"
include "ssfi.mm"
include "sylancl.mm"
include "adantl.mm"
include "wex.mm"
include "simplrl.mm"
include "n0.mm"
include "sylib.mm"
include "abscld.mm"
include "eqid.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "syl.mm"
include "exlimddv.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wor.mm"
include "gtso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "syl3anc.mm"
include "cle.mm"
include "cinf.mm"
include "soss.mm"
include "mp2.mm"
include "fisupg.mm"
include "elrabi.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "lenlt.mm"
include "biimprd.mm"
include "adantll.mm"
include "sylan2.mm"
include "ralimdva.mm"
include "adantrd.mm"
include "reximdva.mm"
include "mpd.mm"
include "lbinfle.mm"
include "df-inf.mm"
include "eqcomi.mm"
include "breq1i.mm"
include "sylibr.mm"
include "sseldi.mm"
include "lenltd.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "ralnex.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "ex.mm"
include "3impa.mm"
include "con2d.mm"
include "imp.mm"

theorem rencldnfilem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint d x
  disjoint d y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  assert |- ( ( ( A C_ RR /\ B e. RR /\ ( A =/= (/) /\ -. B e. A ) ) /\ A. x e. RR+ E. y e. A ( abs ` ( y - B ) ) < x ) -> -. A e. Fin )

  proof
    cA
    cr
    wss
    #
    cB
    cr
    wcel
    #
    cA
    c0
    wne
    #
    cB
    cA
    wcel
    wn
    #
    wa
    #
    w3a
    #
    vy
    cv
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    crp
    wral
    #
    cA
    cfn
    wcel
    #
    wn
    @5
    @13
    @12
    @0
    @1
    @4
    @13
    @12
    wn
    #
    wi
    @0
    @1
    wa
    #
    @4
    wa
    #
    @13
    @14
    @16
    @13
    wa
    #
    @10
    wn
    #
    vy
    cA
    wral
    #
    vx
    crp
    wrex
    #
    @14
    @17
    va
    cv
    #
    vb
    cv
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    wceq
    #
    vb
    cA
    wrex
    #
    va
    cr
    crab
    #
    cr
    clt
    ccnv
    #
    csup
    #
    crp
    wcel
    @8
    @29
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @20
    @17
    @27
    crp
    @29
    @16
    @27
    crp
    wss
    @13
    @16
    vc
    @27
    crp
    vc
    cv
    #
    @27
    wcel
    #
    @33
    cr
    wcel
    #
    @33
    @24
    wceq
    #
    vb
    cA
    wrex
    #
    wa
    @16
    @33
    crp
    wcel
    #
    @26
    @37
    va
    @33
    cr
    @21
    @33
    wceq
    @25
    @36
    vb
    cA
    @21
    @33
    @24
    eqeq1
    rexbidv
    elrab
    @16
    @35
    @37
    @38
    @16
    @35
    wa
    #
    @36
    @38
    vb
    cA
    @39
    @22
    cA
    wcel
    #
    wa
    #
    @38
    @36
    @24
    crp
    wcel
    @41
    @23
    @41
    @22
    cB
    @41
    @22
    @41
    cA
    cr
    @22
    @0
    @1
    @4
    @35
    @40
    simp-4l
    @39
    @40
    simpr
    #
    sseldd
    recnd
    #
    @41
    cB
    @0
    @1
    @4
    @35
    @40
    simp-4r
    recnd
    #
    subcld
    @41
    @23
    cc0
    wne
    #
    @22
    cB
    wceq
    #
    wn
    #
    @41
    @40
    @3
    @47
    @42
    @16
    @3
    @35
    @40
    @15
    @2
    @3
    simprr
    ad2antrr
    @22
    cB
    cA
    nelneq
    syl2anc
    @41
    @22
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @45
    @47
    wb
    @43
    @44
    @48
    @49
    wa
    @46
    @23
    cc0
    @22
    cB
    subeq0
    necon3abid
    syl2anc
    mpbird
    absrpcld
    @33
    @24
    crp
    eleq1
    syl5ibrcom
    rexlimdva
    expimpd
    syl5bi
    ssrdv
    adantr
    @17
    @27
    cfn
    wcel
    #
    @27
    c0
    wne
    #
    @27
    cr
    wss
    #
    @29
    @27
    wcel
    #
    @13
    @50
    @16
    @13
    @26
    va
    cab
    #
    cfn
    wcel
    @27
    @54
    wss
    @50
    vb
    va
    cA
    @24
    abrexfi
    @26
    va
    cr
    rabssab
    @54
    @27
    ssfi
    sylancl
    adantl
    #
    @17
    @6
    cA
    wcel
    #
    @51
    vy
    @17
    @2
    @56
    vy
    wex
    @15
    @2
    @3
    @13
    simplrl
    vy
    cA
    n0
    sylib
    @17
    @56
    wa
    #
    @8
    @27
    wcel
    #
    @51
    @57
    @8
    cr
    wcel
    @8
    @24
    wceq
    #
    vb
    cA
    wrex
    #
    @58
    @57
    @7
    @57
    @6
    cB
    @57
    @6
    @57
    cA
    cr
    @6
    @0
    @1
    @4
    @13
    @56
    simp-4l
    @17
    @56
    simpr
    sseldd
    recnd
    @57
    cB
    @0
    @1
    @4
    @13
    @56
    simp-4r
    recnd
    subcld
    abscld
    #
    @56
    @60
    @17
    @56
    @8
    @8
    wceq
    #
    @60
    @8
    eqid
    @59
    @62
    vb
    @6
    cA
    @22
    @6
    wceq
    #
    @24
    @8
    @8
    @63
    @23
    @7
    cabs
    @22
    @6
    cB
    cmin
    oveq1
    fveq2d
    eqeq2d
    rspcev
    mpan2
    adantl
    @26
    @60
    va
    @8
    cr
    @21
    @8
    wceq
    @25
    @59
    vb
    cA
    @21
    @8
    @24
    eqeq1
    rexbidv
    elrab
    sylanbrc
    #
    @27
    @8
    ne0i
    syl
    exlimddv
    #
    @52
    @17
    @26
    va
    cr
    ssrab2
    #
    a1i
    cr
    @28
    wor
    #
    @50
    @51
    @52
    w3a
    @53
    gtso
    cr
    @27
    @28
    fisupcl
    mpan
    syl3anc
    #
    sseldd
    @17
    @31
    vy
    cA
    @57
    @29
    @8
    cle
    wbr
    #
    @31
    @57
    @27
    cr
    clt
    cinf
    #
    @8
    cle
    wbr
    #
    @69
    @57
    @52
    @33
    vd
    cv
    #
    cle
    wbr
    #
    vd
    @27
    wral
    #
    vc
    @27
    wrex
    #
    @58
    @71
    @52
    @57
    @66
    a1i
    @17
    @75
    @56
    @17
    @33
    @72
    @28
    wbr
    #
    wn
    #
    vd
    @27
    wral
    #
    @72
    @33
    @28
    wbr
    @72
    @9
    @28
    wbr
    vx
    @27
    wrex
    wi
    vd
    @27
    wral
    #
    wa
    #
    vc
    @27
    wrex
    #
    @75
    @17
    @27
    @28
    wor
    #
    @50
    @51
    @81
    @82
    @17
    @52
    @67
    @82
    @66
    gtso
    @27
    cr
    @28
    soss
    mp2
    a1i
    @55
    @65
    vc
    vd
    vx
    @27
    @28
    fisupg
    syl3anc
    @17
    @80
    @74
    vc
    @27
    @34
    @17
    @35
    @80
    @74
    wi
    @26
    va
    @33
    cr
    elrabi
    @17
    @35
    wa
    #
    @78
    @74
    @79
    @83
    @77
    @73
    vd
    @27
    @72
    @27
    wcel
    @83
    @72
    cr
    wcel
    #
    @77
    @73
    wi
    #
    @26
    va
    @72
    cr
    elrabi
    @35
    @84
    @85
    @17
    @77
    @72
    @33
    clt
    wbr
    #
    wn
    #
    @35
    @84
    wa
    #
    @73
    @76
    @86
    @33
    @72
    clt
    vc
    vex
    vd
    vex
    brcnv
    notbii
    @88
    @73
    @87
    @33
    @72
    lenlt
    biimprd
    syl5bi
    adantll
    sylan2
    ralimdva
    adantrd
    sylan2
    reximdva
    mpd
    adantr
    @64
    vc
    vd
    @8
    @27
    lbinfle
    syl3anc
    @29
    @70
    @8
    cle
    @70
    @29
    @27
    cr
    clt
    df-inf
    eqcomi
    breq1i
    sylibr
    @57
    @29
    @8
    @17
    @29
    cr
    wcel
    @56
    @17
    @27
    cr
    @29
    @66
    @68
    sseldi
    adantr
    @61
    lenltd
    mpbid
    ralrimiva
    @19
    @32
    vx
    @29
    crp
    @9
    @29
    wceq
    #
    @18
    @31
    vy
    cA
    @89
    @10
    @30
    @9
    @29
    @8
    clt
    breq2
    notbid
    ralbidv
    rspcev
    syl2anc
    @20
    @11
    wn
    #
    vx
    crp
    wrex
    @14
    @19
    @90
    vx
    crp
    @10
    vy
    cA
    ralnex
    rexbii
    @11
    vx
    crp
    rexnal
    bitri
    sylib
    ex
    3impa
    con2d
    imp
end
