include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cn.mm"
include "wral.mm"
include "ciun.mm"
include "cv.mm"
include "csb.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cdif.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "nfcv.mm"
include "cbviun.mm"
include "csbeq1.mm"
include "iundisj.mm"
include "eqtri.mm"
include "cvv.mm"
include "difexg.mm"
include "ralimi.mm"
include "dfiun2g.mm"
include "syl.mm"
include "syl5eq.mm"
include "sylbi.mm"
include "eqid.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "cfv.mm"
include "cin.mm"
include "covol.mm"
include "wa.mm"
include "rspc.mm"
include "impcom.mm"
include "cfn.mm"
include "fzofi.mm"
include "wss.mm"
include "wi.mm"
include "fzossnn.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "adantr.mm"
include "finiunmbl.mm"
include "sylancr.mm"
include "difmbl.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "wdisj.mm"
include "iundisj2.mm"
include "simpr.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "fvmptg.mm"
include "disjeq2dv.mm"
include "mpbiri.mm"
include "voliunlem2.mm"
include "eqeltrd.mm"

theorem iunmbl
  let cA: class A
  let vn: setvar n
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. n e. NN A e. dom vol -> U_ n e. NN A e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    vn
    cn
    wral
    #
    vn
    cn
    cA
    ciun
    #
    vk
    cn
    vn
    vk
    cv
    #
    cA
    csb
    #
    vm
    c1
    @4
    cfzo
    co
    #
    vn
    vm
    cv
    #
    cA
    csb
    #
    ciun
    #
    cdif
    #
    cmpt
    #
    crn
    #
    cuni
    #
    @0
    @2
    @3
    vy
    cv
    #
    @10
    wceq
    vk
    cn
    wrex
    vy
    cab
    #
    cuni
    #
    @13
    @2
    @5
    @0
    wcel
    #
    vk
    cn
    wral
    #
    @3
    @16
    wceq
    @1
    @17
    vn
    vk
    cn
    @1
    vk
    nfv
    vn
    @5
    @0
    vn
    @4
    cA
    nfcsb1v
    #
    nfel1
    #
    vn
    vk
    weq
    cA
    @5
    @0
    vn
    @4
    cA
    csbeq1a
    #
    eleq1d
    #
    cbvral
    @18
    @3
    vk
    cn
    @10
    ciun
    #
    @16
    @3
    vk
    cn
    @5
    ciun
    @23
    vn
    vk
    cn
    cA
    @5
    vk
    cA
    nfcv
    @19
    @21
    cbviun
    @5
    @8
    vm
    vk
    vn
    @4
    @7
    cA
    csbeq1
    iundisj
    eqtri
    @18
    @10
    cvv
    wcel
    #
    vk
    cn
    wral
    @23
    @16
    wceq
    @17
    @24
    vk
    cn
    @5
    @9
    @0
    difexg
    ralimi
    vk
    vy
    cn
    @10
    cvv
    dfiun2g
    syl
    syl5eq
    sylbi
    @12
    @15
    vk
    vy
    cn
    @10
    @11
    @11
    eqid
    #
    rnmpt
    unieqi
    syl6eqr
    @2
    vx
    vi
    vy
    @11
    vy
    cn
    vx
    cv
    @14
    @11
    cfv
    cin
    covol
    cfv
    cmpt
    #
    @2
    vk
    cn
    @10
    @0
    @11
    @2
    @4
    cn
    wcel
    #
    wa
    #
    @17
    @9
    @0
    wcel
    #
    @10
    @0
    wcel
    @27
    @2
    @17
    @1
    @17
    vn
    @4
    cn
    @20
    @22
    rspc
    impcom
    @28
    @6
    cfn
    wcel
    @8
    @0
    wcel
    #
    vm
    @6
    wral
    #
    @29
    c1
    @4
    fzofi
    @2
    @31
    @27
    @2
    @30
    vm
    cn
    wral
    #
    @31
    @1
    @30
    vn
    vm
    cn
    @1
    vm
    nfv
    vn
    @8
    @0
    vn
    @7
    cA
    nfcsb1v
    nfel1
    vn
    vm
    weq
    cA
    @8
    @0
    vn
    @7
    cA
    csbeq1a
    eleq1d
    cbvral
    @6
    cn
    wss
    @32
    @31
    wi
    @4
    fzossnn
    @30
    vm
    @6
    cn
    ssralv
    ax-mp
    sylbi
    adantr
    @6
    @8
    vm
    finiunmbl
    sylancr
    @5
    @9
    difmbl
    syl2anc
    @25
    fmptd
    @2
    vi
    cn
    vi
    cv
    #
    @11
    cfv
    #
    wdisj
    vi
    cn
    vn
    @33
    cA
    csb
    #
    vm
    c1
    @33
    cfzo
    co
    #
    @8
    ciun
    #
    cdif
    #
    wdisj
    @35
    @8
    vm
    vi
    vn
    @33
    @7
    cA
    csbeq1
    iundisj2
    @2
    vi
    cn
    @34
    @38
    @2
    @33
    cn
    wcel
    #
    wa
    #
    @39
    @38
    cvv
    wcel
    #
    @34
    @38
    wceq
    @2
    @39
    simpr
    @40
    @35
    @0
    wcel
    #
    @41
    @39
    @2
    @42
    @1
    @42
    vn
    @33
    cn
    vn
    @35
    @0
    vn
    @33
    cA
    nfcsb1v
    nfel1
    vn
    vi
    weq
    cA
    @35
    @0
    vn
    @33
    cA
    csbeq1a
    eleq1d
    rspc
    impcom
    @35
    @37
    @0
    difexg
    syl
    vk
    @33
    @10
    @38
    cn
    cvv
    @11
    vk
    vi
    weq
    #
    @5
    @35
    @9
    @37
    vn
    @4
    @33
    cA
    csbeq1
    @43
    vm
    @6
    @36
    @8
    @4
    @33
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    @25
    fvmptg
    syl2anc
    disjeq2dv
    mpbiri
    @26
    eqid
    voliunlem2
    eqeltrd
end
