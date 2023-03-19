include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cmpt.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "chmeo.mm"
include "wa.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "wceq.mm"
include "adantr.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "opeq1.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "vex.mm"
include "xpsn.mm"
include "vtoclg.mm"
include "syl.mm"
include "syl5eqr.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "ctop.mm"
include "ctopon.mm"
include "cfv.mm"
include "topontop.mm"
include "fsnd.mm"
include "cnmptid.mm"
include "elsni.mm"
include "fveq2d.mm"
include "fvsng.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "ptcn.mm"
include "eqeltrrd.mm"
include "cuni.mm"
include "cmap.mm"
include "simprr.mm"
include "adantrr.mm"
include "eqtr4d.mm"
include "wf.mm"
include "simprl.mm"
include "eqid.mm"
include "fmptd.mm"
include "wb.mm"
include "toponmax.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "fveq1d.mm"
include "eqtr2d.mm"
include "jca.mm"
include "mpbid.mm"
include "snidg.mm"
include "ffvelrnd.mm"
include "fsn2g.mm"
include "simprd.mm"
include "opeq2d.mm"
include "impbida.mm"
include "mptcnv.mm"
include "cpt.mm"
include "xpsng.mm"
include "eqcomd.mm"
include "syl5eq.mm"
include "pttoponconst.mm"
include "toponuni.mm"
include "mpteq1d.mm"
include "eqtrd.mm"
include "ptpjcn.mm"
include "mp3an2i.mm"
include "eleqtrd.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem pt1hmeo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vy: setvar y
  assume pt1hmeo.j: |- K = ( Xt_ ` { <. A , J >. } )
  assume pt1hmeo.a: |- ( ph -> A e. V )
  assume pt1hmeo.r: |- ( ph -> J e. ( TopOn ` X ) )

  disjoint A x
  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint X x
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A y
  disjoint J k
  disjoint J y
  disjoint K y
  disjoint k ph
  disjoint ph y
  disjoint X k
  disjoint X y
  assert |- ( ph -> ( x e. X |-> { <. A , x >. } ) e. ( J Homeo K ) )

  proof
    wph
    vx
    cX
    cA
    vx
    cv
    #
    cop
    #
    csn
    #
    cmpt
    #
    cJ
    cK
    ccn
    co
    #
    wcel
    @3
    ccnv
    #
    cK
    cJ
    ccn
    co
    #
    wcel
    @3
    cJ
    cK
    chmeo
    co
    wcel
    wph
    vx
    cX
    vk
    cA
    csn
    #
    @0
    cmpt
    #
    cmpt
    @3
    @4
    wph
    vx
    cX
    @8
    @2
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @8
    @7
    @0
    csn
    #
    cxp
    #
    @2
    vk
    @7
    @0
    fconstmpt
    @10
    cA
    cV
    wcel
    #
    @12
    @2
    wceq
    #
    wph
    @13
    @9
    pt1hmeo.a
    adantr
    vk
    cv
    #
    csn
    #
    @11
    cxp
    #
    @15
    @0
    cop
    #
    csn
    #
    wceq
    @14
    vk
    cA
    cV
    @15
    cA
    wceq
    #
    @17
    @12
    @19
    @2
    @20
    @16
    @7
    @11
    @15
    cA
    sneq
    xpeq1d
    @20
    @18
    @1
    @15
    cA
    @0
    opeq1
    sneqd
    eqeq12d
    @15
    @0
    vk
    vex
    vx
    vex
    xpsn
    vtoclg
    syl
    syl5eqr
    #
    mpteq2dva
    wph
    vx
    @0
    vk
    cA
    cJ
    cop
    csn
    #
    @7
    cJ
    cK
    cvv
    cX
    pt1hmeo.j
    pt1hmeo.r
    @7
    cvv
    wcel
    #
    wph
    cA
    snex
    #
    a1i
    #
    wph
    cA
    cJ
    cV
    ctop
    pt1hmeo.a
    wph
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    ctop
    wcel
    pt1hmeo.r
    cX
    cJ
    topontop
    syl
    fsnd
    #
    wph
    @15
    @7
    wcel
    #
    wa
    #
    vx
    cX
    @0
    cmpt
    #
    cJ
    cJ
    ccn
    co
    #
    cJ
    @15
    @22
    cfv
    #
    ccn
    co
    wph
    @31
    @32
    wcel
    @29
    wph
    vx
    cJ
    cX
    pt1hmeo.r
    cnmptid
    adantr
    @30
    @33
    cJ
    cJ
    ccn
    @29
    wph
    @33
    cA
    @22
    cfv
    #
    cJ
    @29
    @15
    cA
    @22
    @15
    cA
    elsni
    fveq2d
    wph
    @13
    @27
    @34
    cJ
    wceq
    pt1hmeo.a
    pt1hmeo.r
    cA
    cJ
    cV
    @26
    fvsng
    syl2anc
    #
    sylan9eqr
    oveq2d
    eleqtrrd
    ptcn
    eqeltrrd
    wph
    @5
    vy
    cK
    cuni
    #
    cA
    vy
    cv
    #
    cfv
    #
    cmpt
    #
    @6
    wph
    @5
    vy
    cX
    @7
    cmap
    co
    #
    @38
    cmpt
    @39
    wph
    vx
    vy
    cX
    @2
    @40
    @38
    wph
    @9
    @37
    @2
    wceq
    #
    wa
    #
    @37
    @40
    wcel
    #
    @0
    @38
    wceq
    #
    wa
    #
    wph
    @42
    wa
    #
    @43
    @44
    @46
    @37
    @8
    @40
    @46
    @37
    @2
    @8
    wph
    @9
    @41
    simprr
    #
    wph
    @9
    @8
    @2
    wceq
    @41
    @21
    adantrr
    eqtr4d
    @46
    @8
    @40
    wcel
    #
    @7
    cX
    @8
    wf
    #
    @46
    vk
    @7
    @0
    cX
    @8
    @46
    @9
    @29
    wph
    @9
    @41
    simprl
    #
    adantr
    @8
    eqid
    fmptd
    @46
    cX
    cJ
    wcel
    #
    @23
    @48
    @49
    wb
    wph
    @51
    @42
    wph
    @27
    @51
    pt1hmeo.r
    cX
    cJ
    toponmax
    syl
    #
    adantr
    @24
    cX
    @7
    @8
    cJ
    cvv
    elmapg
    sylancl
    mpbird
    eqeltrd
    @46
    @38
    cA
    @2
    cfv
    #
    @0
    @46
    cA
    @37
    @2
    @47
    fveq1d
    @46
    @13
    @9
    @53
    @0
    wceq
    wph
    @13
    @42
    pt1hmeo.a
    adantr
    @50
    cA
    @0
    cV
    cX
    fvsng
    syl2anc
    eqtr2d
    jca
    wph
    @45
    wa
    #
    @9
    @41
    @54
    @0
    @38
    cX
    wph
    @43
    @44
    simprr
    #
    @54
    @7
    cX
    cA
    @37
    @54
    @43
    @7
    cX
    @37
    wf
    #
    wph
    @43
    @44
    simprl
    @54
    @51
    @23
    @43
    @56
    wb
    wph
    @51
    @45
    @52
    adantr
    @24
    cX
    @7
    @37
    cJ
    cvv
    elmapg
    sylancl
    mpbid
    #
    wph
    cA
    @7
    wcel
    #
    @45
    wph
    @13
    @58
    pt1hmeo.a
    cA
    cV
    snidg
    syl
    #
    adantr
    ffvelrnd
    eqeltrd
    @54
    @37
    cA
    @38
    cop
    #
    csn
    #
    @2
    @54
    @38
    cX
    wcel
    #
    @37
    @61
    wceq
    #
    @54
    @56
    @62
    @63
    wa
    #
    @57
    @54
    @13
    @56
    @64
    wb
    wph
    @13
    @45
    pt1hmeo.a
    adantr
    cA
    cX
    @37
    cV
    fsn2g
    syl
    mpbid
    simprd
    @54
    @1
    @60
    @54
    @0
    @38
    cA
    @55
    opeq2d
    sneqd
    eqtr4d
    jca
    impbida
    mptcnv
    wph
    vy
    @40
    @36
    @38
    wph
    cK
    @40
    ctopon
    cfv
    #
    wcel
    @40
    @36
    wceq
    wph
    cK
    @7
    cJ
    csn
    cxp
    #
    cpt
    cfv
    #
    @65
    wph
    cK
    @22
    cpt
    cfv
    @67
    pt1hmeo.j
    wph
    @22
    @66
    cpt
    wph
    @66
    @22
    wph
    @13
    @27
    @66
    @22
    wceq
    pt1hmeo.a
    pt1hmeo.r
    cA
    cJ
    cV
    @26
    xpsng
    syl2anc
    eqcomd
    fveq2d
    syl5eq
    wph
    @23
    @27
    @67
    @65
    wcel
    @25
    pt1hmeo.r
    @7
    cJ
    @67
    cvv
    cX
    @67
    eqid
    pttoponconst
    syl2anc
    eqeltrd
    @40
    cK
    toponuni
    syl
    mpteq1d
    eqtrd
    wph
    @39
    cK
    @34
    ccn
    co
    #
    @6
    @23
    wph
    @7
    ctop
    @22
    wf
    @58
    @39
    @68
    wcel
    @24
    @28
    @59
    vy
    @7
    @22
    cA
    cK
    cvv
    @36
    @36
    eqid
    pt1hmeo.j
    ptpjcn
    mp3an2i
    wph
    @34
    cJ
    cK
    ccn
    @35
    oveq2d
    eleqtrd
    eqeltrd
    @3
    cJ
    cK
    ishmeo
    sylanbrc
end
