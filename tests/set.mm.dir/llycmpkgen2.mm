include "ctop.mm"
include "wcel.mm"
include "ckgen.mm"
include "cfv.mm"
include "wss.mm"
include "crn.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "csn.mm"
include "cnei.mm"
include "cuni.mm"
include "elssuni.mm"
include "adantl.mm"
include "wceq.mm"
include "kgenuni.mm"
include "syl.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "cdif.mm"
include "cnt.mm"
include "cin.mm"
include "ad3antrrr.mm"
include "difss.mm"
include "ntropn.mm"
include "sylancl.mm"
include "simprl.mm"
include "neii1.mm"
include "syl2anc.mm"
include "inopn.mm"
include "syl3anc.mm"
include "cun.mm"
include "inss1.mm"
include "simplr.mm"
include "ntrss2.mm"
include "wb.mm"
include "snssd.mm"
include "neiint.mm"
include "mpbid.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "sseldd.mm"
include "elind.mm"
include "simpllr.mm"
include "simprr.mm"
include "kgeni.mm"
include "cvv.mm"
include "resttop.mm"
include "inss2.mm"
include "restuni.mm"
include "syl5sseq.mm"
include "eqid.mm"
include "isopn3.mm"
include "a1i.mm"
include "restntr.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "undif3.mm"
include "incom.mm"
include "difeq2i.mm"
include "difin.mm"
include "eqtri.mm"
include "syl5ss.mm"
include "ssequn1.mm"
include "sylib.mm"
include "difeq1d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "sslin.mm"
include "c0.mm"
include "difss2d.mm"
include "reldisj.mm"
include "mpbird.mm"
include "inssdif0.mm"
include "sstrd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "ralrimiva.mm"
include "ex.mm"
include "eltop2.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "iskgen2.mm"
include "sylanbrc.mm"

theorem llycmpkgen2
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vz: setvar z
  assume iskgen3.1: |- X = U. J
  assume llycmpkgen2.2: |- ( ph -> J e. Top )
  assume llycmpkgen2.3: |- ( ( ph /\ x e. X ) -> E. k e. ( ( nei ` J ) ` { x } ) ( J |`t k ) e. Comp )

  disjoint k x
  disjoint J k
  disjoint J x
  disjoint k ph
  disjoint ph x
  disjoint X k
  disjoint k u
  disjoint k z
  disjoint u x
  disjoint u z
  disjoint J u
  disjoint x z
  disjoint J z
  disjoint ph u
  disjoint X z
  assert |- ( ph -> J e. ran kGen )

  proof
    wph
    cJ
    ctop
    wcel
    #
    cJ
    ckgen
    cfv
    #
    cJ
    wss
    cJ
    ckgen
    crn
    wcel
    llycmpkgen2.2
    wph
    vu
    @1
    cJ
    wph
    vu
    cv
    #
    @1
    wcel
    #
    vx
    cv
    #
    vz
    cv
    #
    wcel
    #
    @5
    @2
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    vx
    @2
    wral
    #
    @2
    cJ
    wcel
    #
    wph
    @3
    @10
    wph
    @3
    wa
    #
    @9
    vx
    @2
    @12
    @4
    @2
    wcel
    #
    wa
    #
    cJ
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    @9
    vk
    @4
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    @12
    @13
    @4
    cX
    wcel
    #
    @17
    vk
    @19
    wrex
    #
    @12
    @2
    cX
    @4
    @12
    @2
    @1
    cuni
    #
    cX
    @3
    @2
    @22
    wss
    wph
    @2
    @1
    elssuni
    adantl
    wph
    cX
    @22
    wceq
    #
    @3
    wph
    @0
    @23
    llycmpkgen2.2
    cJ
    cX
    iskgen3.1
    kgenuni
    syl
    adantr
    sseqtr4d
    sselda
    #
    wph
    @20
    @21
    @3
    llycmpkgen2.3
    adantlr
    syldan
    @14
    @15
    @19
    wcel
    #
    @17
    wa
    #
    wa
    #
    cX
    @15
    @2
    cdif
    #
    cdif
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    @15
    @30
    cfv
    #
    cin
    #
    cJ
    wcel
    #
    @4
    @33
    wcel
    #
    @33
    @2
    wss
    #
    @9
    @27
    @0
    @31
    cJ
    wcel
    #
    @32
    cJ
    wcel
    #
    @34
    wph
    @0
    @3
    @13
    @26
    llycmpkgen2.2
    ad3antrrr
    #
    @27
    @0
    @29
    cX
    wss
    #
    @37
    @39
    cX
    @28
    difss
    #
    @29
    cJ
    cX
    iskgen3.1
    ntropn
    sylancl
    @27
    @0
    @15
    cX
    wss
    #
    @38
    @39
    @27
    @0
    @25
    @42
    @39
    @14
    @25
    @17
    simprl
    #
    @18
    cJ
    @15
    cX
    iskgen3.1
    neii1
    syl2anc
    #
    @15
    cJ
    cX
    iskgen3.1
    ntropn
    syl2anc
    @31
    @32
    cJ
    inopn
    syl3anc
    @27
    @31
    @32
    @4
    @27
    @4
    @2
    @15
    cin
    #
    cX
    @15
    cdif
    cun
    #
    @30
    cfv
    #
    @31
    @27
    @47
    @15
    cin
    #
    @47
    @4
    @47
    @15
    inss1
    @27
    @4
    @45
    @48
    @27
    @2
    @15
    @4
    @12
    @13
    @26
    simplr
    @27
    @32
    @15
    @4
    @27
    @0
    @42
    @32
    @15
    wss
    #
    @39
    @44
    @15
    cJ
    cX
    iskgen3.1
    ntrss2
    syl2anc
    #
    @27
    @18
    @32
    wss
    #
    @4
    @32
    wcel
    @27
    @25
    @51
    @43
    @27
    @0
    @18
    cX
    wss
    @42
    @25
    @51
    wb
    @39
    @27
    @4
    cX
    @14
    @20
    @26
    @24
    adantr
    snssd
    @44
    @18
    cJ
    @15
    cX
    iskgen3.1
    neiint
    syl3anc
    mpbid
    @4
    @32
    vx
    vex
    snss
    sylibr
    #
    sseldd
    elind
    @27
    @45
    @16
    cnt
    cfv
    cfv
    #
    @45
    @48
    @27
    @45
    @16
    wcel
    #
    @53
    @45
    wceq
    #
    @27
    @3
    @17
    @54
    wph
    @3
    @13
    @26
    simpllr
    @14
    @25
    @17
    simprr
    @2
    cJ
    @15
    kgeni
    syl2anc
    @27
    @16
    ctop
    wcel
    #
    @45
    @16
    cuni
    #
    wss
    @54
    @55
    wb
    @27
    @0
    @15
    cvv
    wcel
    @56
    @39
    vk
    vex
    @15
    cJ
    cvv
    resttop
    sylancl
    @27
    @15
    @45
    @57
    @2
    @15
    inss2
    #
    @27
    @0
    @42
    @15
    @57
    wceq
    @39
    @44
    @15
    cJ
    cX
    iskgen3.1
    restuni
    syl2anc
    syl5sseq
    @45
    @16
    @57
    @57
    eqid
    isopn3
    syl2anc
    mpbid
    @27
    @0
    @42
    @45
    @15
    wss
    #
    @53
    @48
    wceq
    @39
    @44
    @59
    @27
    @58
    a1i
    @45
    cJ
    @16
    cX
    @15
    iskgen3.1
    @16
    eqid
    restntr
    syl3anc
    eqtr3d
    eleqtrd
    sseldi
    @27
    @46
    @29
    @30
    @27
    @46
    @45
    cX
    cun
    #
    @28
    cdif
    #
    @29
    @46
    @60
    @15
    @45
    cdif
    #
    cdif
    @61
    @45
    cX
    @15
    undif3
    @62
    @28
    @60
    @62
    @15
    @15
    @2
    cin
    #
    cdif
    @28
    @45
    @63
    @15
    @2
    @15
    incom
    difeq2i
    @15
    @2
    difin
    eqtri
    difeq2i
    eqtri
    @27
    @60
    cX
    @28
    @27
    @45
    cX
    wss
    @60
    cX
    wceq
    @27
    @45
    @15
    cX
    @58
    @44
    syl5ss
    @45
    cX
    ssequn1
    sylib
    difeq1d
    syl5eq
    fveq2d
    eleqtrd
    @52
    elind
    @27
    @33
    @31
    @15
    cin
    #
    @2
    @27
    @49
    @33
    @64
    wss
    @50
    @32
    @15
    @31
    sslin
    syl
    @27
    @31
    @28
    cin
    c0
    wceq
    #
    @64
    @2
    wss
    @27
    @65
    @31
    @29
    wss
    #
    @27
    @0
    @40
    @66
    @39
    @41
    @29
    cJ
    cX
    iskgen3.1
    ntrss2
    sylancl
    #
    @27
    @31
    cX
    wss
    @65
    @66
    wb
    @27
    @31
    cX
    @28
    @67
    difss2d
    @31
    @28
    cX
    reldisj
    syl
    mpbird
    @31
    @15
    @2
    inssdif0
    sylibr
    sstrd
    @8
    @35
    @36
    wa
    vz
    @33
    cJ
    @5
    @33
    wceq
    @6
    @35
    @7
    @36
    @5
    @33
    @4
    eleq2
    @5
    @33
    @2
    sseq1
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    ralrimiva
    ex
    wph
    @0
    @11
    @10
    wb
    llycmpkgen2.2
    vx
    vz
    @2
    cJ
    eltop2
    syl
    sylibrd
    ssrdv
    cJ
    iskgen2
    sylanbrc
end
