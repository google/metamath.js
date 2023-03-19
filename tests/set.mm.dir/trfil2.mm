include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "c0.mm"
include "wn.mm"
include "cv.mm"
include "cin.mm"
include "wne.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cpw.mm"
include "wb.mm"
include "wceq.mm"
include "simpr.mm"
include "sseqin2.mm"
include "sylib.mm"
include "cvv.mm"
include "simpl.mm"
include "id.mm"
include "filtop.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "adantr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "elpwi.mm"
include "vex.mm"
include "inex1.mm"
include "a1i.mm"
include "elrest.mm"
include "syldan.mm"
include "sseq1d.mm"
include "rexxfr2d.mm"
include "cun.mm"
include "indir.mm"
include "simplr.mm"
include "df-ss.mm"
include "uneq2d.mm"
include "simprr.mm"
include "ssequn1.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "simplll.mm"
include "simpllr.mm"
include "syl2anc.mm"
include "simprl.mm"
include "filelss.mm"
include "sstrd.mm"
include "unssd.mm"
include "ssun1.mm"
include "filss.mm"
include "syl13anc.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "ex.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "simpll.mm"
include "filin.mm"
include "3expb.mm"
include "adantlr.mm"
include "ralrimivva.mm"
include "ineq12.mm"
include "inindir.mm"
include "syl6eqr.mm"
include "adantll.mm"
include "eleq1d.mm"
include "ralxfr2d.mm"
include "mpbird.mm"
include "w3a.mm"
include "isfil2.mm"
include "restsspw.mm"
include "3anass.mm"
include "mpbiran.mm"
include "3anbi1i.mm"
include "3bitri.mm"
include "anass.mm"
include "ancom.mm"
include "baib.mm"
include "syl12anc.mm"
include "nesym.mm"
include "ralbii.mm"
include "dfrex2.mm"
include "syl6bb.mm"
include "con2bid.mm"
include "syl5bb.mm"
include "bitr4d.mm"

theorem trfil2
  let vv: setvar v
  let cA: class A
  let cL: class L
  let cY: class Y
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A v
  disjoint L v
  disjoint Y v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint L u
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint Y u
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( L e. ( Fil ` Y ) /\ A C_ Y ) -> ( ( L |`t A ) e. ( Fil ` A ) <-> A. v e. L ( v i^i A ) =/= (/) ) )

  proof
    cL
    cY
    cfil
    cfv
    #
    wcel
    #
    cA
    cY
    wss
    #
    wa
    #
    cL
    cA
    crest
    co
    #
    cA
    cfil
    cfv
    wcel
    #
    c0
    @4
    wcel
    #
    wn
    #
    vv
    cv
    cA
    cin
    #
    c0
    wne
    #
    vv
    cL
    wral
    #
    @3
    cA
    @4
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    wss
    #
    vy
    @4
    wrex
    #
    @13
    @4
    wcel
    #
    wi
    #
    vx
    cA
    cpw
    #
    wral
    #
    @13
    @12
    cin
    #
    @4
    wcel
    #
    vy
    @4
    wral
    #
    vx
    @4
    wral
    #
    @5
    @7
    wb
    @3
    cY
    cA
    cin
    #
    cA
    @4
    @3
    @2
    @24
    cA
    wceq
    @1
    @2
    simpr
    cA
    cY
    sseqin2
    sylib
    @3
    @1
    cA
    cvv
    wcel
    #
    cY
    cL
    wcel
    #
    @24
    @4
    wcel
    @1
    @2
    simpl
    @2
    @2
    @26
    @25
    @1
    @2
    id
    cL
    cY
    filtop
    #
    cA
    cY
    cL
    ssexg
    syl2anr
    #
    @1
    @26
    @2
    @27
    adantr
    cY
    cA
    cL
    @0
    cvv
    elrestr
    syl3anc
    eqeltrrd
    @3
    @17
    vx
    @18
    @13
    @18
    wcel
    @13
    cA
    wss
    #
    @3
    @17
    @13
    cA
    elpwi
    @3
    @29
    @17
    @3
    @29
    wa
    #
    @15
    vu
    cv
    #
    cA
    cin
    #
    @13
    wss
    #
    vu
    cL
    wrex
    @16
    @30
    @14
    @33
    vy
    vu
    @32
    @4
    cL
    cvv
    @32
    cvv
    wcel
    #
    @30
    @31
    cL
    wcel
    #
    wa
    @31
    cA
    vu
    vex
    inex1
    #
    a1i
    @3
    @12
    @4
    wcel
    @12
    @32
    wceq
    #
    vu
    cL
    wrex
    wb
    #
    @29
    @1
    @2
    @25
    @38
    @28
    vu
    @12
    cA
    cL
    @0
    cvv
    elrest
    syldan
    #
    adantr
    @30
    @37
    wa
    @12
    @32
    @13
    @30
    @37
    simpr
    sseq1d
    rexxfr2d
    @30
    @33
    @16
    vu
    cL
    @30
    @35
    @33
    wa
    #
    wa
    #
    @31
    @13
    cun
    #
    cA
    cin
    #
    @13
    @4
    @41
    @43
    @32
    @13
    cA
    cin
    #
    cun
    #
    @13
    @31
    @13
    cA
    indir
    @41
    @45
    @32
    @13
    cun
    #
    @13
    @41
    @44
    @13
    @32
    @41
    @29
    @44
    @13
    wceq
    @3
    @29
    @40
    simplr
    #
    @13
    cA
    df-ss
    sylib
    uneq2d
    @41
    @33
    @46
    @13
    wceq
    @30
    @35
    @33
    simprr
    @32
    @13
    ssequn1
    sylib
    eqtrd
    syl5eq
    @41
    @1
    @25
    @42
    cL
    wcel
    #
    @43
    @4
    wcel
    @1
    @2
    @29
    @40
    simplll
    #
    @41
    @1
    @2
    @25
    @49
    @1
    @2
    @29
    @40
    simpllr
    #
    @28
    syl2anc
    @41
    @1
    @35
    @42
    cY
    wss
    @31
    @42
    wss
    #
    @48
    @49
    @30
    @35
    @33
    simprl
    #
    @41
    @31
    @13
    cY
    @41
    @1
    @35
    @31
    cY
    wss
    @49
    @52
    @31
    cL
    cY
    filelss
    syl2anc
    @41
    @13
    cA
    cY
    @47
    @50
    sstrd
    unssd
    @51
    @41
    @31
    @13
    ssun1
    a1i
    @31
    @42
    cL
    cY
    filss
    syl13anc
    @42
    cA
    cL
    @0
    cvv
    elrestr
    syl3anc
    eqeltrrd
    rexlimdvaa
    sylbid
    ex
    syl5
    ralrimiv
    @3
    @23
    vz
    cv
    #
    @31
    cin
    #
    cA
    cin
    #
    @4
    wcel
    #
    vu
    cL
    wral
    #
    vz
    cL
    wral
    @3
    @56
    vz
    vu
    cL
    cL
    @3
    @53
    cL
    wcel
    #
    @35
    wa
    #
    wa
    @1
    @25
    @54
    cL
    wcel
    #
    @56
    @1
    @2
    @59
    simpll
    @3
    @25
    @59
    @28
    adantr
    @1
    @59
    @60
    @2
    @1
    @58
    @35
    @60
    @53
    @31
    cL
    cY
    filin
    3expb
    adantlr
    @54
    cA
    cL
    @0
    cvv
    elrestr
    syl3anc
    ralrimivva
    @3
    @22
    @57
    vx
    vz
    @53
    cA
    cin
    #
    @4
    cL
    cvv
    @61
    cvv
    wcel
    @3
    @58
    wa
    @53
    cA
    vz
    vex
    inex1
    a1i
    @1
    @2
    @25
    @16
    @13
    @61
    wceq
    #
    vz
    cL
    wrex
    wb
    @28
    vz
    @13
    cA
    cL
    @0
    cvv
    elrest
    syldan
    @3
    @62
    wa
    #
    @21
    @56
    vy
    vu
    @32
    @4
    cL
    cvv
    @34
    @63
    @35
    wa
    @36
    a1i
    @3
    @38
    @62
    @39
    adantr
    @63
    @37
    wa
    @20
    @55
    @4
    @62
    @37
    @20
    @55
    wceq
    @3
    @62
    @37
    wa
    @20
    @61
    @32
    cin
    @55
    @13
    @61
    @12
    @32
    ineq12
    @53
    @31
    cA
    inindir
    syl6eqr
    adantll
    eleq1d
    ralxfr2d
    ralxfr2d
    mpbird
    @5
    @11
    @19
    @23
    wa
    #
    wa
    #
    @7
    @5
    @7
    @11
    wa
    #
    @64
    wa
    #
    @7
    @65
    wa
    @65
    @7
    wa
    @5
    @4
    @18
    wss
    #
    @7
    @11
    w3a
    #
    @19
    @23
    w3a
    @66
    @19
    @23
    w3a
    @67
    vx
    vy
    @4
    cA
    isfil2
    @69
    @66
    @19
    @23
    @69
    @68
    @66
    cA
    cL
    restsspw
    @68
    @7
    @11
    3anass
    mpbiran
    3anbi1i
    @66
    @19
    @23
    3anass
    3bitri
    @7
    @11
    @64
    anass
    @7
    @65
    ancom
    3bitri
    baib
    syl12anc
    @10
    c0
    @8
    wceq
    #
    wn
    #
    vv
    cL
    wral
    #
    @3
    @7
    @9
    @71
    vv
    cL
    @8
    c0
    nesym
    ralbii
    @3
    @6
    @72
    @3
    @6
    @70
    vv
    cL
    wrex
    #
    @72
    wn
    @1
    @2
    @25
    @6
    @73
    wb
    @28
    vv
    c0
    cA
    cL
    @0
    cvv
    elrest
    syldan
    @70
    vv
    cL
    dfrex2
    syl6bb
    con2bid
    syl5bb
    bitr4d
end
