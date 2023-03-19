include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "creg.mm"
include "cv.mm"
include "wn.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ccld.mm"
include "wa.mm"
include "cuni.mm"
include "simp1r.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp1l.mm"
include "toponuni.mm"
include "syl.mm"
include "eleqtrd.mm"
include "simp3.mm"
include "eqid.mm"
include "regsep2.mm"
include "syl13anc.mm"
include "3expia.mm"
include "ralrimivva.mm"
include "ctop.mm"
include "ccl.mm"
include "topontop.mm"
include "adantr.mm"
include "cdif.mm"
include "difeq1d.mm"
include "opncld.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "eleq2.mm"
include "notbid.mm"
include "eldif.mm"
include "baibr.mm"
include "con1bid.mm"
include "sylan9bb.mm"
include "simpl.mm"
include "sseq1d.mm"
include "3anbi1d.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "rspcv.mm"
include "ralcom3.mm"
include "toponss.mm"
include "sselda.mm"
include "simprr2.mm"
include "ad3antrrr.mm"
include "simprll.mm"
include "syl2anc.mm"
include "incom.mm"
include "simprr3.mm"
include "syl5eq.mm"
include "wb.mm"
include "simplll.mm"
include "simprlr.mm"
include "reldisj.mm"
include "mpbid.mm"
include "clsss2.mm"
include "simprr1.mm"
include "difcom.mm"
include "sylib.mm"
include "sstrd.mm"
include "jca.mm"
include "expr.mm"
include "anassrs.mm"
include "reximdva.mm"
include "rexlimdva.mm"
include "embantd.mm"
include "ralimdva.mm"
include "syl5bi.mm"
include "syld.mm"
include "ralrimdva.mm"
include "imp.mm"
include "isreg.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem isreg2
  let vx: setvar x
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vp: setvar p
  let vc: setvar c
  let vy: setvar y

  disjoint c o
  disjoint c p
  disjoint c x
  disjoint J c
  disjoint o p
  disjoint o x
  disjoint J o
  disjoint p x
  disjoint J p
  disjoint J x
  disjoint X c
  disjoint X o
  disjoint X p
  disjoint X x
  disjoint c y
  disjoint o y
  disjoint p y
  disjoint x y
  disjoint J y
  disjoint X y
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Reg <-> A. c e. ( Clsd ` J ) A. x e. X ( -. x e. c -> E. o e. J E. p e. J ( c C_ o /\ x e. p /\ ( o i^i p ) = (/) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    creg
    wcel
    #
    vx
    cv
    #
    vc
    cv
    #
    wcel
    #
    wn
    #
    @3
    vo
    cv
    #
    wss
    #
    @2
    vp
    cv
    #
    wcel
    #
    @6
    @8
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vp
    cJ
    wrex
    vo
    cJ
    wrex
    #
    wi
    #
    vx
    cX
    wral
    #
    vc
    cJ
    ccld
    cfv
    #
    wral
    #
    @0
    @1
    wa
    #
    @14
    vc
    vx
    @16
    cX
    @18
    @3
    @16
    wcel
    #
    @2
    cX
    wcel
    #
    wa
    #
    @5
    @13
    @18
    @21
    @5
    w3a
    #
    @1
    @19
    @2
    cJ
    cuni
    #
    wcel
    @5
    @13
    @0
    @1
    @21
    @5
    simp1r
    @18
    @19
    @20
    @5
    simp2l
    @22
    @2
    cX
    @23
    @18
    @19
    @20
    @5
    simp2r
    @22
    @0
    cX
    @23
    wceq
    #
    @0
    @1
    @21
    @5
    simp1l
    cX
    cJ
    toponuni
    #
    syl
    eleqtrd
    @18
    @21
    @5
    simp3
    vo
    vp
    @2
    @3
    cJ
    @23
    @23
    eqid
    #
    regsep2
    syl13anc
    3expia
    ralrimivva
    @0
    @17
    wa
    cJ
    ctop
    wcel
    #
    @9
    @8
    cJ
    ccl
    cfv
    cfv
    #
    vy
    cv
    #
    wss
    #
    wa
    #
    vp
    cJ
    wrex
    #
    vx
    @29
    wral
    #
    vy
    cJ
    wral
    #
    @1
    @0
    @27
    @17
    cX
    cJ
    topontop
    #
    adantr
    @0
    @17
    @34
    @0
    @17
    @33
    vy
    cJ
    @0
    @29
    cJ
    wcel
    #
    wa
    #
    @17
    @2
    @29
    wcel
    #
    cX
    @29
    cdif
    #
    @6
    wss
    #
    @9
    @11
    w3a
    #
    vp
    cJ
    wrex
    #
    vo
    cJ
    wrex
    #
    wi
    #
    vx
    cX
    wral
    #
    @33
    @37
    @39
    @16
    wcel
    @17
    @45
    wi
    @37
    @39
    @23
    @29
    cdif
    #
    @16
    @37
    cX
    @23
    @29
    @0
    @24
    @36
    @25
    adantr
    difeq1d
    @0
    @27
    @36
    @46
    @16
    wcel
    @35
    @29
    cJ
    @23
    @26
    opncld
    sylan
    eqeltrd
    @15
    @45
    vc
    @39
    @16
    @3
    @39
    wceq
    #
    @14
    @44
    vx
    cX
    @47
    @20
    wa
    #
    @5
    @38
    @13
    @43
    @47
    @5
    @2
    @39
    wcel
    #
    wn
    @20
    @38
    @47
    @4
    @49
    @3
    @39
    @2
    eleq2
    notbid
    @20
    @38
    @49
    @49
    @20
    @38
    wn
    @2
    cX
    @29
    eldif
    baibr
    con1bid
    sylan9bb
    @48
    @12
    @41
    vo
    vp
    cJ
    cJ
    @48
    @7
    @40
    @9
    @11
    @48
    @3
    @39
    @6
    @47
    @20
    simpl
    sseq1d
    3anbi1d
    2rexbidv
    imbi12d
    ralbidva
    rspcv
    syl
    @45
    @20
    @43
    wi
    #
    vx
    @29
    wral
    @37
    @33
    @43
    vx
    cX
    @29
    ralcom3
    @37
    @50
    @32
    vx
    @29
    @37
    @38
    wa
    #
    @20
    @43
    @32
    @37
    @29
    cX
    @2
    @29
    cJ
    cX
    toponss
    sselda
    @51
    @42
    @32
    vo
    cJ
    @51
    @6
    cJ
    wcel
    #
    wa
    @41
    @31
    vp
    cJ
    @51
    @52
    @8
    cJ
    wcel
    #
    @41
    @31
    wi
    @51
    @52
    @53
    wa
    #
    @41
    @31
    @51
    @54
    @41
    wa
    #
    wa
    #
    @9
    @30
    @40
    @9
    @11
    @54
    @51
    simprr2
    @56
    @28
    cX
    @6
    cdif
    #
    @29
    @56
    @57
    @16
    wcel
    @8
    @57
    wss
    #
    @28
    @57
    wss
    @56
    @57
    @23
    @6
    cdif
    #
    @16
    @56
    cX
    @23
    @6
    @0
    @24
    @36
    @38
    @55
    @25
    ad3antrrr
    difeq1d
    @56
    @27
    @52
    @59
    @16
    wcel
    @0
    @27
    @36
    @38
    @55
    @35
    ad3antrrr
    @51
    @52
    @53
    @41
    simprll
    @6
    cJ
    @23
    @26
    opncld
    syl2anc
    eqeltrd
    @56
    @8
    @6
    cin
    #
    c0
    wceq
    #
    @58
    @56
    @60
    @10
    c0
    @8
    @6
    incom
    @40
    @9
    @11
    @54
    @51
    simprr3
    syl5eq
    @56
    @8
    cX
    wss
    #
    @61
    @58
    wb
    @56
    @0
    @53
    @62
    @0
    @36
    @38
    @55
    simplll
    @51
    @52
    @53
    @41
    simprlr
    @8
    cJ
    cX
    toponss
    syl2anc
    @8
    @6
    cX
    reldisj
    syl
    mpbid
    @57
    @8
    cJ
    @23
    @26
    clsss2
    syl2anc
    @56
    @40
    @57
    @29
    wss
    @40
    @9
    @11
    @54
    @51
    simprr1
    cX
    @29
    @6
    difcom
    sylib
    sstrd
    jca
    expr
    anassrs
    reximdva
    rexlimdva
    embantd
    ralimdva
    syl5bi
    syld
    ralrimdva
    imp
    vy
    vx
    vp
    cJ
    isreg
    sylanbrc
    impbida
end
