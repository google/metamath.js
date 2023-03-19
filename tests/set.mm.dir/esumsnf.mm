include "csn.mm"
include "cesum.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "wceq.mm"
include "df-esum.mm"
include "a1i.mm"
include "cfn.mm"
include "eqid.mm"
include "wcel.mm"
include "snfi.mm"
include "wf.mm"
include "cop.mm"
include "cv.mm"
include "elsni.mm"
include "sylan2.mm"
include "mpteq2dva.mm"
include "wa.mm"
include "fmptsn.mm"
include "nfcv.mm"
include "eqidd.mm"
include "cbvmpt.mm"
include "syl6eqr.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "wb.mm"
include "fsng.mm"
include "mpbird.mm"
include "snssd.mm"
include "fssd.mm"
include "cpr.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "cif.mm"
include "cpw.mm"
include "cin.mm"
include "cres.mm"
include "cgsu.mm"
include "crn.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "cle.mm"
include "elxrge0.mm"
include "sylib.mm"
include "simpld.mm"
include "suppr.mm"
include "syl3anc.mm"
include "c0.mm"
include "0fin.mm"
include "reseq2.mm"
include "res0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "xrge00.mm"
include "gsum0.mm"
include "adantl.mm"
include "wss.mm"
include "ssid.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "xrge0base.mm"
include "cmnd.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "cmnmnd.mm"
include "nfv.mm"
include "gsumsnfd.mm"
include "sylan9eqr.mm"
include "fmptpr.mm"
include "pwsn.mm"
include "prssi.mm"
include "mp2an.mm"
include "eqsstri.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqtri.mm"
include "mpteq12i.mm"
include "rneqd.mm"
include "rnpropg.mm"
include "eqtr3d.mm"
include "supeq1d.mm"
include "wn.mm"
include "wo.mm"
include "simprd.mm"
include "xrlenlt.mm"
include "mpbid.mm"
include "jca.mm"
include "olcd.mm"
include "eqif.mm"
include "sylibr.mm"
include "3eqtr4rd.mm"
include "xrge0tsmsd.mm"
include "unieqd.mm"
include "unisng.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem esumsnf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vl: setvar l
  assume esumsnf.0: |- F/_ k B
  assume esumsnf.1: |- ( ( ph /\ k = M ) -> A = B )
  assume esumsnf.2: |- ( ph -> M e. V )
  assume esumsnf.3: |- ( ph -> B e. ( 0 [,] +oo ) )

  disjoint M k
  disjoint k ph
  disjoint A x
  disjoint B l
  disjoint B x
  disjoint l x
  disjoint M l
  disjoint M x
  disjoint k l
  disjoint k x
  disjoint ph x
  assert |- ( ph -> sum* k e. { M } A = B )

  proof
    wph
    cM
    csn
    #
    cA
    vk
    cesum
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vk
    @0
    cA
    cmpt
    #
    ctsu
    co
    #
    cuni
    #
    cB
    csn
    #
    cuni
    #
    cB
    @1
    @6
    wceq
    wph
    @0
    cA
    vk
    df-esum
    a1i
    wph
    @5
    @7
    wph
    @0
    cB
    @4
    @3
    cfn
    vx
    @3
    eqid
    @0
    cfn
    wcel
    #
    wph
    cM
    snfi
    #
    a1i
    #
    wph
    @0
    @7
    @2
    @4
    wph
    @0
    @7
    @4
    wf
    #
    @4
    cM
    cB
    cop
    csn
    #
    wceq
    #
    wph
    @4
    vk
    @0
    cB
    cmpt
    #
    @13
    wph
    vk
    @0
    cA
    cB
    vk
    cv
    #
    @0
    wcel
    wph
    @16
    cM
    wceq
    cA
    cB
    wceq
    @16
    cM
    elsni
    esumsnf.1
    sylan2
    mpteq2dva
    wph
    cM
    cV
    wcel
    #
    cB
    @2
    wcel
    #
    @13
    @15
    wceq
    esumsnf.2
    esumsnf.3
    @17
    @18
    wa
    @13
    vl
    @0
    cB
    cmpt
    @15
    vl
    cM
    cB
    cV
    @2
    fmptsn
    vk
    vl
    @0
    cB
    cB
    vl
    cB
    nfcv
    esumsnf.0
    @16
    vl
    cv
    wceq
    cB
    eqidd
    cbvmpt
    syl6eqr
    syl2anc
    eqtr4d
    wph
    @17
    @18
    @12
    @14
    wb
    esumsnf.2
    esumsnf.3
    cM
    cB
    cV
    @2
    @4
    fsng
    syl2anc
    mpbird
    wph
    cB
    @2
    esumsnf.3
    snssd
    fssd
    wph
    cc0
    cB
    cpr
    #
    cxr
    clt
    csup
    #
    cB
    cc0
    clt
    wbr
    #
    cc0
    cB
    cif
    #
    vx
    @0
    cpw
    #
    cfn
    cin
    #
    @3
    @4
    vx
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    cB
    wph
    cxr
    clt
    wor
    #
    cc0
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @20
    @22
    wceq
    @30
    wph
    xrltso
    a1i
    @31
    wph
    0xr
    a1i
    #
    wph
    @32
    cc0
    cB
    cle
    wbr
    #
    wph
    @18
    @32
    @34
    wa
    esumsnf.3
    cB
    elxrge0
    sylib
    #
    simpld
    #
    cxr
    cc0
    cB
    clt
    suppr
    syl3anc
    wph
    cxr
    @29
    @19
    clt
    wph
    c0
    cc0
    cop
    @0
    cB
    cop
    cpr
    #
    crn
    #
    @29
    @19
    wph
    @37
    @28
    wph
    @37
    vx
    c0
    @0
    cpr
    #
    @27
    cmpt
    @28
    wph
    vx
    c0
    @0
    cc0
    cB
    @27
    cfn
    cfn
    cxr
    @2
    c0
    cfn
    wcel
    #
    wph
    0fin
    a1i
    #
    @11
    @33
    esumsnf.3
    @25
    c0
    wceq
    #
    @27
    cc0
    wceq
    wph
    @42
    @27
    @3
    c0
    cgsu
    co
    cc0
    @42
    @26
    c0
    @3
    cgsu
    @42
    @26
    @4
    c0
    cres
    c0
    @25
    c0
    @4
    reseq2
    @4
    res0
    syl6eq
    oveq2d
    @3
    cc0
    xrge00
    gsum0
    syl6eq
    adantl
    @25
    @0
    wceq
    #
    wph
    @27
    @3
    @4
    cgsu
    co
    cB
    @43
    @26
    @4
    @3
    cgsu
    @43
    @26
    @4
    @0
    cres
    #
    @4
    @25
    @0
    @4
    reseq2
    @0
    @0
    wss
    @44
    @4
    wceq
    @0
    ssid
    vk
    @0
    @0
    cA
    resmpt
    ax-mp
    syl6eq
    oveq2d
    wph
    cA
    @2
    cB
    vk
    @3
    cM
    cV
    xrge0base
    @3
    cmnd
    wcel
    #
    wph
    @3
    ccmn
    wcel
    @45
    xrge0cmn
    @3
    cmnmnd
    ax-mp
    a1i
    esumsnf.2
    esumsnf.3
    esumsnf.1
    wph
    vk
    nfv
    esumsnf.0
    gsumsnfd
    sylan9eqr
    fmptpr
    vx
    @24
    @27
    @39
    @27
    @24
    @23
    @39
    @23
    cfn
    wss
    @24
    @23
    wceq
    @23
    @39
    cfn
    cM
    pwsn
    #
    @40
    @9
    @39
    cfn
    wss
    0fin
    @10
    c0
    @0
    cfn
    prssi
    mp2an
    eqsstri
    @23
    cfn
    df-ss
    mpbi
    @46
    eqtri
    @27
    eqid
    mpteq12i
    syl6eqr
    rneqd
    wph
    @40
    @9
    @38
    @19
    wceq
    @41
    @11
    c0
    @0
    cc0
    cB
    cfn
    cfn
    rnpropg
    syl2anc
    eqtr3d
    supeq1d
    wph
    @21
    cB
    cc0
    wceq
    wa
    #
    @21
    wn
    #
    cB
    cB
    wceq
    #
    wa
    #
    wo
    cB
    @22
    wceq
    wph
    @50
    @47
    wph
    @48
    @49
    wph
    @34
    @48
    wph
    @32
    @34
    @35
    simprd
    wph
    @31
    @32
    @34
    @48
    wb
    @33
    @36
    cc0
    cB
    xrlenlt
    syl2anc
    mpbid
    wph
    cB
    eqidd
    jca
    olcd
    @21
    cB
    cc0
    cB
    eqif
    sylibr
    3eqtr4rd
    xrge0tsmsd
    unieqd
    wph
    @18
    @8
    cB
    wceq
    esumsnf.3
    cB
    @2
    unisng
    syl
    3eqtrd
end
