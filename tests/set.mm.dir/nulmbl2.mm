include "cv.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cvol.mm"
include "cdm.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cr.mm"
include "wcel.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wi.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "1rp.mm"
include "ne0ii.mm"
include "r19.2z.mm"
include "mpan.mm"
include "simprl.mm"
include "mblss.mm"
include "adantr.mm"
include "sstrd.mm"
include "rexlimiva.mm"
include "rexlimivw.mm"
include "syl.mm"
include "inss1.mm"
include "a1i.mm"
include "elpwi.mm"
include "simpr.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "difssd.mm"
include "readdcld.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "simprrr.mm"
include "ovollecl.mm"
include "simprrl.mm"
include "sslin.mm"
include "syl5ss.mm"
include "ovolss.mm"
include "syl2anc.mm"
include "cun.mm"
include "ssdifssd.mm"
include "unssd.mm"
include "ovolun.mm"
include "syl22anc.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "ssdif.mm"
include "ax-mp.mm"
include "difundir.mm"
include "sseqtri.mm"
include "difun1.mm"
include "wceq.mm"
include "ssequn2.mm"
include "sylib.mm"
include "difeq2d.mm"
include "syl5eqr.mm"
include "uneq1d.mm"
include "syl5sseq.mm"
include "letrd.mm"
include "le2addd.mm"
include "mblsplit.mm"
include "oveq1d.mm"
include "recnd.mm"
include "addassd.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "difss.mm"
include "sylancr.mm"
include "leadd2dd.mm"
include "rexlimdvaa.mm"
include "ralimdva.mm"
include "impcom.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "simprr.mm"
include "xralrple.mm"
include "mpbird.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ismbl2.mm"
include "sylanbrc.mm"

theorem nulmbl2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( A. x e. RR+ E. y e. dom vol ( A C_ y /\ ( vol* ` y ) <_ x ) -> A e. dom vol )

  proof
    cA
    vy
    cv
    #
    wss
    #
    @0
    covol
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    wa
    #
    vy
    cvol
    cdm
    #
    wrex
    #
    vx
    crp
    wral
    #
    cA
    cr
    wss
    #
    vz
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @10
    cA
    cin
    #
    covol
    cfv
    #
    @10
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @11
    cle
    wbr
    #
    wi
    #
    vz
    cr
    cpw
    #
    wral
    cA
    @6
    wcel
    @8
    @7
    vx
    crp
    wrex
    #
    @9
    crp
    c0
    wne
    @8
    @21
    c1
    crp
    1rp
    ne0ii
    @7
    vx
    crp
    r19.2z
    mpan
    @7
    @9
    vx
    crp
    @5
    @9
    vy
    @6
    @0
    @6
    wcel
    #
    @5
    wa
    #
    cA
    @0
    cr
    @22
    @1
    @4
    simprl
    @22
    @0
    cr
    wss
    #
    @5
    @0
    mblss
    adantr
    #
    sstrd
    rexlimiva
    rexlimivw
    syl
    @8
    @19
    vz
    @20
    @8
    @10
    @20
    wcel
    #
    @12
    @18
    @8
    @26
    @12
    wa
    #
    wa
    #
    @18
    @17
    @11
    @3
    caddc
    co
    #
    cle
    wbr
    #
    vx
    crp
    wral
    #
    @27
    @8
    @31
    @27
    @7
    @30
    vx
    crp
    @27
    @3
    crp
    wcel
    #
    wa
    #
    @5
    @30
    vy
    @6
    @33
    @23
    wa
    #
    @17
    @11
    @0
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @29
    @27
    @17
    cr
    wcel
    #
    @32
    @23
    @27
    @14
    @16
    @27
    @13
    @10
    wss
    #
    @10
    cr
    wss
    #
    @12
    @14
    cr
    wcel
    #
    @39
    @27
    @10
    cA
    inss1
    a1i
    @26
    @40
    @12
    @10
    cr
    elpwi
    adantr
    #
    @26
    @12
    simpr
    #
    @13
    @10
    ovolsscl
    syl3anc
    #
    @27
    @15
    @10
    wss
    @40
    @12
    @16
    cr
    wcel
    #
    @27
    @10
    cA
    difssd
    @42
    @43
    @15
    @10
    ovolsscl
    syl3anc
    #
    readdcld
    #
    ad2antrr
    @34
    @11
    @36
    @27
    @12
    @32
    @23
    @43
    ad2antrr
    #
    @34
    @35
    @0
    wss
    #
    @24
    @2
    cr
    wcel
    #
    @36
    cr
    wcel
    #
    @34
    @0
    cA
    difssd
    @23
    @24
    @33
    @25
    adantl
    #
    @34
    @24
    @3
    cr
    wcel
    #
    @4
    @50
    @52
    @32
    @53
    @27
    @23
    @3
    rpre
    ad2antlr
    #
    @33
    @22
    @1
    @4
    simprrr
    #
    @0
    @3
    ovollecl
    syl3anc
    #
    @35
    @0
    ovolsscl
    syl3anc
    #
    readdcld
    @34
    @11
    @3
    @48
    @54
    readdcld
    @34
    @17
    @10
    @0
    cin
    #
    covol
    cfv
    #
    @10
    @0
    cdif
    #
    covol
    cfv
    #
    @36
    caddc
    co
    #
    caddc
    co
    #
    @37
    cle
    @34
    @14
    @16
    @59
    @62
    @27
    @41
    @32
    @23
    @44
    ad2antrr
    @27
    @45
    @32
    @23
    @46
    ad2antrr
    #
    @34
    @58
    @10
    wss
    #
    @40
    @12
    @59
    cr
    wcel
    @65
    @34
    @10
    @0
    inss1
    #
    a1i
    @27
    @40
    @32
    @23
    @42
    ad2antrr
    #
    @48
    @58
    @10
    ovolsscl
    syl3anc
    #
    @34
    @61
    @36
    @34
    @60
    @10
    wss
    @40
    @12
    @61
    cr
    wcel
    #
    @34
    @10
    @0
    difssd
    @67
    @48
    @60
    @10
    ovolsscl
    syl3anc
    #
    @57
    readdcld
    #
    @34
    @13
    @58
    wss
    #
    @58
    cr
    wss
    @14
    @59
    cle
    wbr
    @34
    @1
    @72
    @33
    @22
    @1
    @4
    simprrl
    #
    cA
    @0
    @10
    sslin
    syl
    @34
    @58
    @10
    cr
    @66
    @67
    syl5ss
    @13
    @58
    ovolss
    syl2anc
    @34
    @16
    @60
    @35
    cun
    #
    covol
    cfv
    #
    @62
    @64
    @34
    @74
    cr
    wss
    #
    @62
    cr
    wcel
    @75
    @62
    cle
    wbr
    #
    @75
    cr
    wcel
    @34
    @60
    @35
    cr
    @34
    @10
    cr
    @0
    @67
    ssdifssd
    #
    @34
    @0
    cr
    cA
    @52
    ssdifssd
    #
    unssd
    #
    @71
    @34
    @60
    cr
    wss
    @69
    @35
    cr
    wss
    @51
    @77
    @78
    @70
    @79
    @57
    @60
    @35
    ovolun
    syl22anc
    #
    @74
    @62
    ovollecl
    syl3anc
    @71
    @34
    @15
    @74
    wss
    @76
    @16
    @75
    cle
    wbr
    @34
    @60
    cA
    cdif
    #
    @35
    cun
    #
    @15
    @74
    @15
    @60
    @0
    cun
    #
    cA
    cdif
    #
    @83
    @10
    @84
    wss
    @15
    @85
    wss
    @10
    @10
    @0
    cun
    @84
    @10
    @0
    ssun1
    @10
    @0
    undif1
    sseqtr4i
    @10
    @84
    cA
    ssdif
    ax-mp
    @60
    @0
    cA
    difundir
    sseqtri
    @34
    @82
    @60
    @35
    @34
    @82
    @10
    @0
    cA
    cun
    #
    cdif
    @60
    @10
    @0
    cA
    difun1
    @34
    @86
    @0
    @10
    @34
    @1
    @86
    @0
    wceq
    @73
    cA
    @0
    ssequn2
    sylib
    difeq2d
    syl5eqr
    uneq1d
    syl5sseq
    @80
    @15
    @74
    ovolss
    syl2anc
    @81
    letrd
    le2addd
    @34
    @37
    @59
    @61
    caddc
    co
    #
    @36
    caddc
    co
    @63
    @34
    @11
    @87
    @36
    caddc
    @34
    @22
    @40
    @12
    @11
    @87
    wceq
    @33
    @22
    @5
    simprl
    @67
    @48
    @0
    @10
    mblsplit
    syl3anc
    oveq1d
    @34
    @59
    @61
    @36
    @34
    @59
    @68
    recnd
    @34
    @61
    @70
    recnd
    @34
    @36
    @57
    recnd
    addassd
    eqtrd
    breqtrrd
    @34
    @36
    @3
    @11
    @57
    @54
    @48
    @34
    @36
    @2
    @3
    @57
    @56
    @54
    @34
    @49
    @24
    @36
    @2
    cle
    wbr
    @0
    cA
    difss
    @52
    @35
    @0
    ovolss
    sylancr
    @55
    letrd
    leadd2dd
    letrd
    rexlimdvaa
    ralimdva
    impcom
    @28
    @17
    cxr
    wcel
    @12
    @18
    @31
    wb
    @28
    @17
    @27
    @38
    @8
    @47
    adantl
    rexrd
    @8
    @26
    @12
    simprr
    vx
    @17
    @11
    xralrple
    syl2anc
    mpbird
    expr
    ralrimiva
    vz
    cA
    ismbl2
    sylanbrc
end
