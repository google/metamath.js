include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "cn.mm"
include "wral.mm"
include "wdisj.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "caddc.mm"
include "cv.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "ciun.mm"
include "cin.mm"
include "covol.mm"
include "wf.mm"
include "simpl.mm"
include "ralimi.mm"
include "adantr.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "wceq.mm"
include "wb.mm"
include "fvmpt2.mm"
include "adantrr.mm"
include "ralimiaa.mm"
include "disjeq2.mm"
include "syl.mm"
include "biimpar.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "fveq2.mm"
include "cbvdisj.mm"
include "nffv.mm"
include "fveq2d.mm"
include "cbvmpt.mm"
include "eleq1d.mm"
include "biimprd.mm"
include "impr.mm"
include "nfv.mm"
include "nfel1.mm"
include "cbvral.mm"
include "voliunlem3.mm"
include "wrex.mm"
include "cab.mm"
include "dfiun2g.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "mpteq12.mm"
include "sylancr.mm"
include "syl6reqr.mm"
include "seqeq3d.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "3eqtr4d.mm"

theorem voliun
  let cA: class A
  let cS: class S
  let vn: setvar n
  let cG: class G
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume voliun.1: |- S = seq 1 ( + , G )
  assume voliun.2: |- G = ( n e. NN |-> ( vol ` A ) )


  assert |- ( ( A. n e. NN ( A e. dom vol /\ ( vol ` A ) e. RR ) /\ Disj_ n e. NN A ) -> ( vol ` U_ n e. NN A ) = sup ( ran S , RR* , < ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vn
    cn
    wral
    #
    vn
    cn
    cA
    wdisj
    #
    wa
    #
    vn
    cn
    cA
    cmpt
    #
    crn
    #
    cuni
    #
    cvol
    cfv
    caddc
    vn
    cn
    vn
    cv
    #
    @8
    cfv
    #
    cvol
    cfv
    #
    cmpt
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    vn
    cn
    cA
    ciun
    #
    cvol
    cfv
    cS
    crn
    #
    cxr
    clt
    csup
    @7
    vx
    @15
    vi
    vm
    @8
    @14
    vm
    cn
    vx
    cv
    #
    vm
    cv
    #
    @8
    cfv
    #
    cin
    covol
    cfv
    cmpt
    #
    @7
    @1
    vn
    cn
    wral
    #
    cn
    @0
    @8
    wf
    @5
    @23
    @6
    @4
    @1
    vn
    cn
    @1
    @3
    simpl
    ralimi
    adantr
    #
    vn
    cn
    @0
    cA
    @8
    @8
    eqid
    #
    fmpt
    sylib
    @7
    vn
    cn
    @12
    wdisj
    #
    vi
    cn
    vi
    cv
    #
    @8
    cfv
    #
    wdisj
    @5
    @26
    @6
    @5
    @12
    cA
    wceq
    #
    vn
    cn
    wral
    @26
    @6
    wb
    @4
    @29
    vn
    cn
    @11
    cn
    wcel
    #
    @1
    @29
    @3
    vn
    cn
    cA
    @0
    @8
    @25
    fvmpt2
    #
    adantrr
    ralimiaa
    vn
    cn
    @12
    cA
    disjeq2
    syl
    biimpar
    vn
    vi
    cn
    @12
    @28
    vi
    @12
    nfcv
    vn
    cn
    cA
    @27
    nffvmpt1
    #
    @11
    @27
    @8
    fveq2
    #
    cbvdisj
    sylib
    @22
    eqid
    @15
    eqid
    vn
    vm
    cn
    @13
    @21
    cvol
    cfv
    vm
    @13
    nfcv
    vn
    @21
    cvol
    vn
    cvol
    nfcv
    #
    vn
    cn
    cA
    @20
    nffvmpt1
    nffv
    @11
    @20
    wceq
    @12
    @21
    cvol
    @11
    @20
    @8
    fveq2
    fveq2d
    cbvmpt
    @7
    @13
    cr
    wcel
    #
    vn
    cn
    wral
    #
    @28
    cvol
    cfv
    #
    cr
    wcel
    #
    vi
    cn
    wral
    @5
    @36
    @6
    @4
    @35
    vn
    cn
    @30
    @1
    @3
    @35
    @30
    @1
    wa
    #
    @35
    @3
    @39
    @13
    @2
    cr
    @39
    @12
    cA
    cvol
    @31
    fveq2d
    #
    eleq1d
    biimprd
    impr
    ralimiaa
    adantr
    @35
    @38
    vn
    vi
    cn
    @35
    vi
    nfv
    vn
    @37
    cr
    vn
    @28
    cvol
    @34
    @32
    nffv
    nfel1
    @11
    @27
    wceq
    #
    @13
    @37
    cr
    @41
    @12
    @28
    cvol
    @33
    fveq2d
    eleq1d
    cbvral
    sylib
    voliunlem3
    @7
    @17
    @10
    cvol
    @7
    @17
    @19
    cA
    wceq
    vn
    cn
    wrex
    vx
    cab
    #
    cuni
    #
    @10
    @7
    @23
    @17
    @43
    wceq
    @24
    vn
    vx
    cn
    cA
    @0
    dfiun2g
    syl
    @9
    @42
    vn
    vx
    cn
    cA
    @8
    @25
    rnmpt
    unieqi
    syl6eqr
    fveq2d
    @7
    cxr
    @18
    @16
    clt
    @7
    cS
    @15
    @7
    cS
    caddc
    cG
    c1
    cseq
    @15
    voliun.1
    @7
    cG
    @14
    caddc
    c1
    @7
    @14
    vn
    cn
    @2
    cmpt
    #
    cG
    @7
    cn
    cn
    wceq
    @13
    @2
    wceq
    #
    vn
    cn
    wral
    #
    @14
    @44
    wceq
    cn
    eqid
    @5
    @46
    @6
    @4
    @45
    vn
    cn
    @30
    @1
    @45
    @3
    @40
    adantrr
    ralimiaa
    adantr
    vn
    cn
    @13
    cn
    @2
    mpteq12
    sylancr
    voliun.2
    syl6reqr
    seqeq3d
    syl5eq
    rneqd
    supeq1d
    3eqtr4d
end
