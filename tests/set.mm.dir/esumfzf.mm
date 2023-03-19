include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "cesum.mm"
include "cxad.mm"
include "cseq.mm"
include "wceq.mm"
include "wi.mm"
include "caddc.mm"
include "nfv.mm"
include "oveq2.mm"
include "esumeq1d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "csn.mm"
include "nfcv.mm"
include "nffv.mm"
include "cbvesum.mm"
include "cz.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "1z.mm"
include "a1i.mm"
include "1nn.mm"
include "ffvelrn.mm"
include "mpan2.mm"
include "esumsn.mm"
include "syl5eq.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "esumeq1.mm"
include "seq1.mm"
include "3eqtr4g.mm"
include "cuz.mm"
include "simpl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "seqp1.mm"
include "syl.mm"
include "adantr.mm"
include "oveq1d.mm"
include "cun.mm"
include "nfci.mm"
include "nff.mm"
include "nfan.mm"
include "fzsuc.mm"
include "ovexd.mm"
include "cvv.mm"
include "snex.mm"
include "cin.mm"
include "c0.mm"
include "fzp1disj.mm"
include "simplr.mm"
include "wss.mm"
include "fzssnn.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "velsn.mm"
include "sylib.mm"
include "simpll.mm"
include "peano2nnd.mm"
include "eqeltrd.mm"
include "esumsplit.mm"
include "oveq2d.mm"
include "3eqtrrd.mm"
include "3eqtr2rd.mm"
include "exp31.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem esumfzf
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vi: setvar i
  let vn: setvar n
  let vx: setvar x
  assume esumfzf.1: |- F/_ k F

  disjoint N k
  disjoint i k
  disjoint i n
  disjoint i x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint F i
  disjoint F n
  disjoint F x
  disjoint N i
  assert |- ( ( F : NN --> ( 0 [,] +oo ) /\ N e. NN ) -> sum* k e. ( 1 ... N ) ( F ` k ) = ( seq 1 ( +e , F ) ` N ) )

  proof
    cN
    cn
    wcel
    cn
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    cF
    cfv
    #
    vk
    cesum
    #
    cN
    cxad
    cF
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    @1
    c1
    vi
    cv
    #
    cfz
    co
    #
    @4
    vk
    cesum
    #
    @9
    @6
    cfv
    #
    wceq
    #
    wi
    @1
    c1
    c1
    cfz
    co
    #
    @4
    vk
    cesum
    #
    c1
    @6
    cfv
    #
    wceq
    #
    wi
    @1
    c1
    vn
    cv
    #
    cfz
    co
    #
    @4
    vk
    cesum
    #
    @18
    @6
    cfv
    #
    wceq
    #
    wi
    @1
    c1
    @18
    c1
    caddc
    co
    #
    cfz
    co
    #
    @4
    vk
    cesum
    #
    @23
    @6
    cfv
    #
    wceq
    #
    wi
    @1
    @8
    wi
    vi
    vn
    cN
    @9
    c1
    wceq
    #
    @13
    @17
    @1
    @28
    @11
    @15
    @12
    @16
    @28
    @10
    @14
    @4
    vk
    @28
    vk
    nfv
    @9
    c1
    c1
    cfz
    oveq2
    esumeq1d
    @9
    c1
    @6
    fveq2
    eqeq12d
    imbi2d
    @9
    @18
    wceq
    #
    @13
    @22
    @1
    @29
    @11
    @20
    @12
    @21
    @29
    @10
    @19
    @4
    vk
    @29
    vk
    nfv
    @9
    @18
    c1
    cfz
    oveq2
    esumeq1d
    @9
    @18
    @6
    fveq2
    eqeq12d
    imbi2d
    @9
    @23
    wceq
    #
    @13
    @27
    @1
    @30
    @11
    @25
    @12
    @26
    @30
    @10
    @24
    @4
    vk
    @30
    vk
    nfv
    @9
    @23
    c1
    cfz
    oveq2
    esumeq1d
    @9
    @23
    @6
    fveq2
    eqeq12d
    imbi2d
    @9
    cN
    wceq
    #
    @13
    @8
    @1
    @31
    @11
    @5
    @12
    @7
    @31
    @10
    @2
    @4
    vk
    @31
    vk
    nfv
    @9
    cN
    c1
    cfz
    oveq2
    esumeq1d
    @9
    cN
    @6
    fveq2
    eqeq12d
    imbi2d
    @1
    c1
    csn
    #
    @4
    vk
    cesum
    #
    c1
    cF
    cfv
    #
    @15
    @16
    @1
    @33
    @32
    vx
    cv
    #
    cF
    cfv
    #
    vx
    cesum
    @34
    @32
    @4
    @36
    vk
    vx
    @3
    @35
    cF
    fveq2
    #
    vx
    @32
    nfcv
    vk
    @32
    nfcv
    vx
    @4
    nfcv
    #
    vk
    @35
    cF
    esumfzf.1
    vk
    @35
    nfcv
    nffv
    #
    cbvesum
    @1
    @36
    @34
    vx
    c1
    cz
    @1
    @35
    c1
    wceq
    #
    wa
    @35
    c1
    cF
    @1
    @40
    simpr
    fveq2d
    c1
    cz
    wcel
    #
    @1
    1z
    a1i
    @1
    c1
    cn
    wcel
    #
    @34
    @0
    wcel
    1nn
    cn
    @0
    c1
    cF
    ffvelrn
    mpan2
    esumsn
    syl5eq
    @14
    @32
    wceq
    #
    @15
    @33
    wceq
    @41
    @43
    1z
    c1
    fzsn
    ax-mp
    @14
    @32
    @4
    vk
    esumeq1
    ax-mp
    @41
    @16
    @34
    wceq
    1z
    cxad
    cF
    c1
    seq1
    ax-mp
    3eqtr4g
    @18
    cn
    wcel
    #
    @1
    @22
    @27
    @44
    @1
    @22
    @27
    @44
    @1
    wa
    #
    @22
    wa
    #
    @26
    @21
    @23
    cF
    cfv
    #
    cxad
    co
    #
    @20
    @47
    cxad
    co
    #
    @25
    @45
    @26
    @48
    wceq
    #
    @22
    @45
    @18
    c1
    cuz
    cfv
    #
    wcel
    #
    @50
    @45
    @18
    cn
    @51
    @44
    @1
    simpl
    #
    nnuz
    syl6eleq
    #
    cxad
    cF
    c1
    @18
    seqp1
    syl
    adantr
    @46
    @20
    @21
    @47
    cxad
    @45
    @22
    simpr
    oveq1d
    @45
    @49
    @25
    wceq
    @22
    @45
    @25
    @19
    @23
    csn
    #
    cun
    #
    @4
    vk
    cesum
    @20
    @55
    @4
    vk
    cesum
    #
    cxad
    co
    @49
    @45
    @24
    @56
    @4
    vk
    @44
    @1
    vk
    @44
    vk
    nfv
    #
    vk
    cn
    @0
    cF
    esumfzf.1
    vk
    vn
    cn
    @58
    nfci
    vk
    @0
    nfcv
    nff
    nfan
    #
    @45
    @52
    @24
    @56
    wceq
    @54
    c1
    @18
    fzsuc
    syl
    esumeq1d
    @45
    @19
    @55
    @4
    vk
    @59
    vk
    @19
    nfcv
    vk
    @55
    nfcv
    #
    @45
    c1
    @18
    cfz
    ovexd
    @55
    cvv
    wcel
    @45
    @23
    snex
    a1i
    @19
    @55
    cin
    c0
    wceq
    @45
    c1
    @18
    fzp1disj
    a1i
    @45
    @3
    @19
    wcel
    #
    wa
    #
    cn
    @0
    @3
    cF
    @44
    @1
    @61
    simplr
    @62
    @19
    cn
    @3
    @42
    @19
    cn
    wss
    1nn
    c1
    @18
    fzssnn
    ax-mp
    @45
    @61
    simpr
    sseldi
    ffvelrnd
    @45
    @3
    @55
    wcel
    #
    wa
    #
    cn
    @0
    @3
    cF
    @44
    @1
    @63
    simplr
    @64
    @3
    @23
    cn
    @64
    @63
    @3
    @23
    wceq
    @45
    @63
    simpr
    vk
    @23
    velsn
    sylib
    @64
    @18
    @44
    @1
    @63
    simpll
    peano2nnd
    eqeltrd
    ffvelrnd
    esumsplit
    @45
    @57
    @47
    @20
    cxad
    @45
    @57
    @55
    @36
    vx
    cesum
    @47
    @55
    @4
    @36
    vk
    vx
    @37
    vx
    @55
    nfcv
    @60
    @38
    @39
    cbvesum
    @45
    @36
    @47
    vx
    @23
    cn
    @45
    @35
    @23
    wceq
    #
    wa
    @35
    @23
    cF
    @45
    @65
    simpr
    fveq2d
    @45
    @18
    @53
    peano2nnd
    #
    @45
    cn
    @0
    @23
    cF
    @44
    @1
    simpr
    @66
    ffvelrnd
    esumsn
    syl5eq
    oveq2d
    3eqtrrd
    adantr
    3eqtr2rd
    exp31
    a2d
    nnind
    impcom
end
