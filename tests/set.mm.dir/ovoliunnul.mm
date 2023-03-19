include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "ciun.mm"
include "c0.mm"
include "wi.mm"
include "iuneq1.mm"
include "0iun.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "ovol0.mm"
include "a1i.mm"
include "wne.mm"
include "csdm.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "reldom.mm"
include "brrelexi.mm"
include "adantr.mm"
include "0sdomg.mm"
include "syl.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "fodomr.mm"
include "expcom.mm"
include "csb.mm"
include "wrex.mm"
include "eliun.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfiun.mm"
include "nfcri.mm"
include "foelrn.mm"
include "ex.mm"
include "csbeq1a.mm"
include "adantl.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "impancom.mm"
include "reximdv.mm"
include "syl6ibr.mm"
include "com23.mm"
include "syld.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "wf.mm"
include "fof.mm"
include "ffvelrnda.mm"
include "simpllr.mm"
include "nfss.mm"
include "nffv.mm"
include "nfeq1.mm"
include "nfan.mm"
include "sseq1d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspc.mm"
include "sylc.mm"
include "simpld.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "cle.mm"
include "csu.mm"
include "caddc.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "eqid.mm"
include "simprd.mm"
include "0re.mm"
include "syl6eqel.mm"
include "cuz.mm"
include "csn.mm"
include "cxp.mm"
include "cli.mm"
include "cdm.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "nnuz.mm"
include "xpeq1i.mm"
include "eqtr3i.mm"
include "seqeq3d.mm"
include "cz.mm"
include "1z.mm"
include "serclim0.mm"
include "seqex.mm"
include "c0ex.mm"
include "breldm.mm"
include "mp2b.mm"
include "ovoliun2.mm"
include "sumeq2dv.mm"
include "cfn.mm"
include "wo.mm"
include "eqimssi.mm"
include "orci.mm"
include "sumz.mm"
include "ax-mp.mm"
include "breqtrd.mm"
include "ovolge0.mm"
include "cxr.mm"
include "ovolcl.mm"
include "0xr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "ovolssnul.mm"
include "syl3anc.mm"
include "exlimdv.mm"
include "sylbird.mm"
include "pm2.61dne.mm"

theorem ovoliunnul
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x

  disjoint A n
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A x
  disjoint B f
  disjoint B k
  disjoint B x
  assert |- ( ( A ~<_ NN /\ A. n e. A ( B C_ RR /\ ( vol* ` B ) = 0 ) ) -> ( vol* ` U_ n e. A B ) = 0 )

  proof
    cA
    cn
    cdom
    wbr
    #
    cB
    cr
    wss
    #
    cB
    covol
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vn
    cA
    wral
    #
    wa
    #
    vn
    cA
    cB
    ciun
    #
    covol
    cfv
    #
    cc0
    wceq
    #
    cA
    c0
    cA
    c0
    wceq
    #
    @9
    wi
    @6
    @10
    @8
    c0
    covol
    cfv
    cc0
    @10
    @7
    c0
    covol
    @10
    @7
    vn
    c0
    cB
    ciun
    c0
    vn
    cA
    c0
    cB
    iuneq1
    vn
    cB
    0iun
    syl6eq
    fveq2d
    ovol0
    syl6eq
    a1i
    @6
    cA
    c0
    wne
    #
    c0
    cA
    csdm
    wbr
    #
    @9
    @6
    cA
    cvv
    wcel
    #
    @12
    @11
    wb
    @0
    @13
    @5
    cA
    cn
    cdom
    reldom
    brrelexi
    adantr
    cA
    cvv
    0sdomg
    syl
    @6
    @12
    cn
    cA
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    @9
    @0
    @12
    @16
    wi
    @5
    @12
    @0
    @16
    cn
    cA
    vf
    fodomr
    expcom
    adantr
    @6
    @15
    @9
    vf
    @6
    @15
    @9
    @6
    @15
    wa
    #
    @7
    vk
    cn
    vn
    vk
    cv
    #
    @14
    cfv
    #
    cB
    csb
    #
    ciun
    #
    wss
    #
    @21
    cr
    wss
    #
    @21
    covol
    cfv
    #
    cc0
    wceq
    #
    @9
    @15
    @22
    @6
    @15
    vx
    @7
    @21
    vx
    cv
    #
    @7
    wcel
    @26
    cB
    wcel
    #
    vn
    cA
    wrex
    @15
    @26
    @21
    wcel
    #
    vn
    @26
    cA
    cB
    eliun
    @15
    @27
    @28
    vn
    cA
    @15
    vn
    nfv
    vn
    vx
    @21
    vk
    vn
    cn
    @20
    vn
    cn
    nfcv
    vn
    @19
    cB
    nfcsb1v
    #
    nfiun
    nfcri
    @15
    vn
    cv
    #
    cA
    wcel
    #
    @30
    @19
    wceq
    #
    vk
    cn
    wrex
    #
    @27
    @28
    wi
    @15
    @31
    @33
    vk
    cn
    cA
    @30
    @14
    foelrn
    ex
    @15
    @27
    @33
    @28
    @15
    @27
    @33
    @28
    wi
    @15
    @27
    wa
    #
    @33
    @26
    @20
    wcel
    #
    vk
    cn
    wrex
    @28
    @34
    @32
    @35
    vk
    cn
    @15
    @32
    @27
    @35
    @15
    @32
    wa
    #
    @27
    @35
    @36
    cB
    @20
    @26
    @32
    cB
    @20
    wceq
    @15
    vn
    @19
    cB
    csbeq1a
    #
    adantl
    eleq2d
    biimpd
    impancom
    reximdv
    vk
    @26
    cn
    @20
    eliun
    syl6ibr
    ex
    com23
    syld
    rexlimd
    syl5bi
    ssrdv
    adantl
    @17
    @20
    cr
    wss
    #
    vk
    cn
    wral
    @23
    @17
    @38
    vk
    cn
    @17
    @18
    cn
    wcel
    #
    wa
    #
    @38
    @20
    covol
    cfv
    #
    cc0
    wceq
    #
    @40
    @19
    cA
    wcel
    @5
    @38
    @42
    wa
    #
    @17
    cn
    cA
    @18
    @14
    @15
    cn
    cA
    @14
    wf
    @6
    cn
    cA
    @14
    fof
    adantl
    ffvelrnda
    @0
    @5
    @15
    @39
    simpllr
    @4
    @43
    vn
    @19
    cA
    @38
    @42
    vn
    vn
    @20
    cr
    @29
    vn
    cr
    nfcv
    nfss
    vn
    @41
    cc0
    vn
    @20
    covol
    vn
    covol
    nfcv
    @29
    nffv
    nfeq1
    nfan
    @32
    @1
    @38
    @3
    @42
    @32
    cB
    @20
    cr
    @37
    sseq1d
    @32
    @2
    @41
    cc0
    @32
    cB
    @20
    covol
    @37
    fveq2d
    eqeq1d
    anbi12d
    rspc
    sylc
    #
    simpld
    #
    ralrimiva
    vk
    cn
    @20
    cr
    iunss
    sylibr
    #
    @17
    @25
    @24
    cc0
    cle
    wbr
    #
    cc0
    @24
    cle
    wbr
    #
    @17
    @24
    cn
    @41
    vk
    csu
    #
    cc0
    cle
    @17
    @20
    caddc
    vk
    cn
    @41
    cmpt
    #
    c1
    cseq
    #
    vk
    @50
    @51
    eqid
    @50
    eqid
    @45
    @40
    @41
    cc0
    cr
    @40
    @38
    @42
    @44
    simprd
    #
    0re
    syl6eqel
    @17
    @51
    caddc
    c1
    cuz
    cfv
    #
    cc0
    csn
    #
    cxp
    #
    c1
    cseq
    #
    cli
    cdm
    #
    @17
    @50
    @55
    caddc
    c1
    @17
    @50
    vk
    cn
    cc0
    cmpt
    #
    @55
    @17
    vk
    cn
    @41
    cc0
    @52
    mpteq2dva
    cn
    @54
    cxp
    @58
    @55
    vk
    cn
    cc0
    fconstmpt
    cn
    @53
    @54
    nnuz
    xpeq1i
    eqtr3i
    syl6eq
    seqeq3d
    c1
    cz
    wcel
    @56
    cc0
    cli
    wbr
    @56
    @57
    wcel
    1z
    c1
    serclim0
    @56
    cc0
    cli
    caddc
    @55
    c1
    seqex
    c0ex
    breldm
    mp2b
    syl6eqel
    ovoliun2
    @17
    @49
    cn
    cc0
    vk
    csu
    #
    cc0
    @17
    cn
    @41
    cc0
    vk
    @52
    sumeq2dv
    cn
    @53
    wss
    #
    cn
    cfn
    wcel
    #
    wo
    @59
    cc0
    wceq
    @60
    @61
    cn
    @53
    nnuz
    eqimssi
    orci
    cn
    vk
    c1
    sumz
    ax-mp
    syl6eq
    breqtrd
    @17
    @23
    @48
    @46
    @21
    ovolge0
    syl
    @17
    @24
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    @25
    @47
    @48
    wa
    wb
    @17
    @23
    @62
    @46
    @21
    ovolcl
    syl
    0xr
    @24
    cc0
    xrletri3
    sylancl
    mpbir2and
    @7
    @21
    ovolssnul
    syl3anc
    ex
    exlimdv
    syld
    sylbird
    pm2.61dne
end
