include "cmnd.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cword.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "csubmnd.mm"
include "cmre.mm"
include "submacs.mm"
include "acsmred.mm"
include "adantr.mm"
include "wceq.mm"
include "wrex.mm"
include "cs1.mm"
include "simpr.mm"
include "s1cld.mm"
include "ssel2.mm"
include "adantll.mm"
include "gsumws1.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "c0g.mm"
include "cplusg.mm"
include "wral.mm"
include "wf.mm"
include "mrccl.mm"
include "sylan.mm"
include "mrcssid.mm"
include "sswrd.mm"
include "sselda.mm"
include "gsumwsubmcl.mm"
include "fmptd.mm"
include "frn.mm"
include "mrcssvd.mm"
include "sstrd.mm"
include "c0.mm"
include "wrd0.mm"
include "gsum0.mm"
include "eqcomi.mm"
include "a1i.mm"
include "sylancr.mm"
include "fvex.mm"
include "cconcat.mm"
include "ccatcl.mm"
include "adantl.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "gsumccat.mm"
include "syl3anc.mm"
include "ovex.mm"
include "ralrimivva.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "raleqi.mm"
include "eleq1d.mm"
include "ralrnmpt.mm"
include "ovexd.mm"
include "mprg.mm"
include "bitri.mm"
include "ralbii.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "3bitri.mm"
include "w3a.mm"
include "issubm.mm"
include "mpbir3and.mm"
include "mrcsscl.mm"
include "eqssd.mm"

theorem gsumwspan
  let vw: setvar w
  let cB: class B
  let cG: class G
  let cK: class K
  let cM: class M
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gsumwspan.b: |- B = ( Base ` M )
  assume gsumwspan.k: |- K = ( mrCls ` ( SubMnd ` M ) )

  disjoint G w
  disjoint B w
  disjoint M w
  disjoint K w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint G v
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint v z
  disjoint B v
  disjoint w z
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint G z
  disjoint M z
  assert |- ( ( M e. Mnd /\ G C_ B ) -> ( K ` G ) = ran ( w e. Word G |-> ( M gsum w ) ) )

  proof
    cM
    cmnd
    wcel
    #
    cG
    cB
    wss
    #
    wa
    #
    cG
    cK
    cfv
    #
    vw
    cG
    cword
    #
    cM
    vw
    cv
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    @2
    cM
    csubmnd
    cfv
    #
    cB
    cmre
    cfv
    wcel
    #
    cG
    @8
    wss
    @8
    @9
    wcel
    #
    @3
    @8
    wss
    @0
    @10
    @1
    @0
    @9
    cB
    cB
    cM
    gsumwspan.b
    submacs
    acsmred
    #
    adantr
    @2
    vx
    cG
    @8
    @2
    vx
    cv
    #
    cG
    wcel
    #
    @13
    @8
    wcel
    #
    @2
    @14
    wa
    #
    @13
    @6
    wceq
    #
    vw
    @4
    wrex
    #
    @15
    @16
    @13
    cs1
    #
    @4
    wcel
    @13
    cM
    @19
    cgsu
    co
    #
    wceq
    #
    @18
    @16
    @13
    cG
    @2
    @14
    simpr
    s1cld
    @16
    @20
    @13
    @16
    @13
    cB
    wcel
    #
    @20
    @13
    wceq
    @1
    @14
    @22
    @0
    cG
    cB
    @13
    ssel2
    adantll
    cB
    @13
    cM
    gsumwspan.b
    gsumws1
    syl
    eqcomd
    @17
    @21
    vw
    @19
    @4
    @5
    @19
    wceq
    @6
    @20
    @13
    @5
    @19
    cM
    cgsu
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @13
    cvv
    wcel
    @15
    @18
    wb
    vx
    vex
    vw
    @4
    @6
    @13
    @7
    cvv
    @7
    eqid
    #
    elrnmpt
    ax-mp
    sylibr
    ex
    ssrdv
    @2
    @11
    @8
    cB
    wss
    #
    cM
    c0g
    cfv
    #
    @8
    wcel
    #
    @13
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @8
    wcel
    #
    vy
    @8
    wral
    #
    vx
    @8
    wral
    #
    @2
    @8
    @3
    cB
    @2
    @4
    @3
    @7
    wf
    @8
    @3
    wss
    @2
    vw
    @4
    @6
    @3
    @7
    @2
    @5
    @4
    wcel
    #
    wa
    @3
    @9
    wcel
    #
    @5
    @3
    cword
    #
    wcel
    @6
    @3
    wcel
    @2
    @34
    @33
    @0
    @10
    @1
    @34
    @12
    @9
    cG
    cK
    cB
    gsumwspan.k
    mrccl
    sylan
    adantr
    @2
    @4
    @35
    @5
    @2
    cG
    @3
    wss
    #
    @4
    @35
    wss
    @0
    @10
    @1
    @36
    @12
    @9
    cG
    cK
    cB
    gsumwspan.k
    mrcssid
    sylan
    cG
    @3
    sswrd
    syl
    sselda
    @3
    cM
    @5
    gsumwsubmcl
    syl2anc
    @23
    fmptd
    @4
    @3
    @7
    frn
    syl
    #
    @0
    @3
    cB
    wss
    @1
    @0
    @9
    cG
    cK
    cB
    @12
    gsumwspan.k
    mrcssvd
    adantr
    sstrd
    @2
    @25
    @6
    wceq
    #
    vw
    @4
    wrex
    #
    @26
    @2
    c0
    @4
    wcel
    @25
    cM
    c0
    cgsu
    co
    #
    wceq
    #
    @39
    cG
    wrd0
    @41
    @2
    @40
    @25
    cM
    @25
    @25
    eqid
    #
    gsum0
    eqcomi
    a1i
    @38
    @41
    vw
    c0
    @4
    @5
    c0
    wceq
    @6
    @40
    @25
    @5
    c0
    cM
    cgsu
    oveq2
    eqeq2d
    rspcev
    sylancr
    @25
    cvv
    wcel
    @26
    @39
    wb
    cM
    c0g
    fvex
    vw
    @4
    @6
    @25
    @7
    cvv
    @23
    elrnmpt
    ax-mp
    sylibr
    @2
    cM
    vz
    cv
    #
    cgsu
    co
    #
    cM
    vv
    cv
    #
    cgsu
    co
    #
    @28
    co
    #
    @8
    wcel
    #
    vv
    @4
    wral
    #
    vz
    @4
    wral
    #
    @32
    @2
    @48
    vz
    vv
    @4
    @4
    @2
    @43
    @4
    wcel
    #
    @45
    @4
    wcel
    #
    wa
    #
    wa
    #
    @47
    @6
    wceq
    #
    vw
    @4
    wrex
    #
    @48
    @54
    @43
    @45
    cconcat
    co
    #
    @4
    wcel
    #
    @47
    cM
    @57
    cgsu
    co
    #
    wceq
    #
    @56
    @53
    @58
    @2
    cG
    @43
    @45
    ccatcl
    adantl
    @54
    @59
    @47
    @54
    @0
    @43
    cB
    cword
    #
    wcel
    @45
    @61
    wcel
    @59
    @47
    wceq
    @0
    @1
    @53
    simpll
    @54
    @4
    @61
    @43
    @1
    @4
    @61
    wss
    @0
    @53
    cG
    cB
    sswrd
    ad2antlr
    #
    @2
    @51
    @52
    simprl
    sseldd
    @54
    @4
    @61
    @45
    @62
    @2
    @51
    @52
    simprr
    sseldd
    cB
    @28
    cM
    @43
    @45
    gsumwspan.b
    @28
    eqid
    #
    gsumccat
    syl3anc
    eqcomd
    @55
    @60
    vw
    @57
    @4
    @5
    @57
    wceq
    @6
    @59
    @47
    @5
    @57
    cM
    cgsu
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @47
    cvv
    wcel
    @48
    @56
    wb
    @44
    @46
    @28
    ovex
    vw
    @4
    @6
    @47
    @7
    cvv
    @23
    elrnmpt
    ax-mp
    sylibr
    ralrimivva
    @32
    @31
    vx
    vz
    @4
    @44
    cmpt
    #
    crn
    #
    wral
    @13
    @46
    @28
    co
    #
    @8
    wcel
    #
    vv
    @4
    wral
    #
    vx
    @65
    wral
    #
    @50
    @31
    vx
    @8
    @65
    @7
    @64
    vw
    vz
    @4
    @6
    @44
    @5
    @43
    cM
    cgsu
    oveq2
    cbvmptv
    rneqi
    raleqi
    @31
    @68
    vx
    @65
    @31
    @30
    vy
    vv
    @4
    @46
    cmpt
    #
    crn
    #
    wral
    #
    @68
    @30
    vy
    @8
    @71
    @7
    @70
    vw
    vv
    @4
    @6
    @46
    @5
    @45
    cM
    cgsu
    oveq2
    cbvmptv
    rneqi
    raleqi
    @46
    cvv
    wcel
    @72
    @68
    wb
    vv
    @4
    @30
    @67
    vv
    vy
    @4
    @46
    @70
    cvv
    @70
    eqid
    @27
    @46
    wceq
    @29
    @66
    @8
    @27
    @46
    @13
    @28
    oveq2
    eleq1d
    ralrnmpt
    @52
    cM
    @45
    cgsu
    ovexd
    mprg
    bitri
    ralbii
    @44
    cvv
    wcel
    @69
    @50
    wb
    vz
    @4
    @68
    @49
    vz
    vx
    @4
    @44
    @64
    cvv
    @64
    eqid
    @13
    @44
    wceq
    #
    @67
    @48
    vv
    @4
    @73
    @66
    @47
    @8
    @13
    @44
    @46
    @28
    oveq1
    eleq1d
    ralbidv
    ralrnmpt
    @51
    cM
    @43
    cgsu
    ovexd
    mprg
    3bitri
    sylibr
    @0
    @11
    @24
    @26
    @32
    w3a
    wb
    @1
    vx
    vy
    cB
    @28
    @8
    cM
    @25
    gsumwspan.b
    @42
    @63
    issubm
    adantr
    mpbir3and
    @9
    cG
    cK
    @8
    cB
    gsumwspan.k
    mrcsscl
    syl3anc
    @37
    eqssd
end
