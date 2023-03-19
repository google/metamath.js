include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprime.mm"
include "cin.mm"
include "cpc.mm"
include "cexp.mm"
include "clog.mm"
include "cfv.mm"
include "cc0.mm"
include "cif.mm"
include "csu.mm"
include "cmul.mm"
include "elin.mm"
include "baib.mm"
include "ifbid.mm"
include "fvif.mm"
include "wceq.mm"
include "log1.mm"
include "ifeq2.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "sumeq2i.mm"
include "wss.mm"
include "cc.mm"
include "wral.mm"
include "inss1.mm"
include "wa.mm"
include "simpr.mm"
include "sseldi.mm"
include "elfznn.mm"
include "syl.mm"
include "inss2.mm"
include "simpl.mm"
include "pccld.mm"
include "nnexpcld.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "recnd.mm"
include "ralrimiva.mm"
include "cuz.mm"
include "cfn.mm"
include "wo.mm"
include "fzfi.mm"
include "olci.mm"
include "sumss2.mm"
include "mpan2.mm"
include "sylancr.mm"
include "crp.mm"
include "cz.mm"
include "nn0zd.mm"
include "relogexp.mm"
include "syl2anc.mm"
include "sumeq2dv.mm"
include "eqtr3d.mm"
include "caddc.mm"
include "cmpt.mm"
include "cseq.mm"
include "adantl.mm"
include "eleq1.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "ifbieq1d.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "adantr.mm"
include "simpll.mm"
include "wn.mm"
include "1nn.mm"
include "a1i.mm"
include "ifclda.mm"
include "fsumser.mm"
include "rpmulcl.mm"
include "ovex.mm"
include "1ex.mm"
include "ifex.mm"
include "eqeltrd.mm"
include "relogmul.mm"
include "eqtr4d.mm"
include "seqhomo.mm"
include "pcprod.mm"
include "3eqtr2d.mm"
include "3eqtr3a.mm"

theorem pclogsum
  let cA: class A
  let vp: setvar p
  let vm: setvar m
  let vn: setvar n

  disjoint A p
  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  assert |- ( A e. NN -> sum_ p e. ( ( 1 ... A ) i^i Prime ) ( ( p pCnt A ) x. ( log ` p ) ) = ( log ` A ) )

  proof
    cA
    cn
    wcel
    #
    c1
    cA
    cfz
    co
    #
    vp
    cv
    #
    @1
    cprime
    cin
    #
    wcel
    #
    @2
    @2
    cA
    cpc
    co
    #
    cexp
    co
    #
    clog
    cfv
    #
    cc0
    cif
    #
    vp
    csu
    #
    @1
    @2
    cprime
    wcel
    #
    @6
    c1
    cif
    #
    clog
    cfv
    #
    vp
    csu
    #
    @3
    @5
    @2
    clog
    cfv
    #
    cmul
    co
    #
    vp
    csu
    #
    cA
    clog
    cfv
    #
    @1
    @8
    @12
    vp
    @2
    @1
    wcel
    #
    @8
    @10
    @7
    cc0
    cif
    #
    @12
    @18
    @4
    @10
    @7
    cc0
    @4
    @18
    @10
    @2
    @1
    cprime
    elin
    baib
    ifbid
    @12
    @10
    @7
    c1
    clog
    cfv
    #
    cif
    #
    @19
    @10
    @6
    c1
    clog
    fvif
    @20
    cc0
    wceq
    @21
    @19
    wceq
    log1
    @10
    @20
    cc0
    @7
    ifeq2
    ax-mp
    eqtri
    syl6eqr
    sumeq2i
    @0
    @3
    @7
    vp
    csu
    #
    @9
    @16
    @0
    @3
    @1
    wss
    #
    @7
    cc
    wcel
    #
    vp
    @3
    wral
    #
    @22
    @9
    wceq
    #
    @1
    cprime
    inss1
    #
    @0
    @24
    vp
    @3
    @0
    @4
    wa
    #
    @7
    @28
    @6
    @28
    @6
    @28
    @2
    @5
    @28
    @18
    @2
    cn
    wcel
    #
    @28
    @3
    @1
    @2
    @27
    @0
    @4
    simpr
    #
    sseldi
    @2
    cA
    elfznn
    #
    syl
    #
    @28
    @2
    cA
    @28
    @3
    cprime
    @2
    @1
    cprime
    inss2
    @30
    sseldi
    @0
    @4
    simpl
    pccld
    #
    nnexpcld
    nnrpd
    relogcld
    recnd
    ralrimiva
    @23
    @25
    wa
    @1
    c1
    cuz
    cfv
    #
    wss
    #
    @1
    cfn
    wcel
    #
    wo
    @26
    @36
    @35
    c1
    cA
    fzfi
    olci
    @3
    @1
    @7
    vp
    c1
    sumss2
    mpan2
    sylancr
    @0
    @3
    @7
    @15
    vp
    @28
    @2
    crp
    wcel
    #
    @5
    cz
    wcel
    @7
    @15
    wceq
    @28
    @2
    @32
    nnrpd
    @28
    @5
    @33
    nn0zd
    @2
    @5
    relogexp
    syl2anc
    sumeq2dv
    eqtr3d
    @0
    @13
    cA
    caddc
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    @38
    @38
    cA
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    clog
    cfv
    #
    cmpt
    #
    c1
    cseq
    cfv
    cA
    cmul
    vn
    cn
    @42
    cmpt
    #
    c1
    cseq
    cfv
    #
    clog
    cfv
    @17
    @0
    @12
    vp
    @44
    c1
    cA
    @0
    @18
    wa
    #
    @29
    @2
    @44
    cfv
    #
    @12
    wceq
    @18
    @29
    @0
    @31
    adantl
    #
    vn
    @2
    @43
    @12
    cn
    @44
    @38
    @2
    wceq
    #
    @42
    @11
    clog
    @50
    @39
    @10
    @41
    @6
    c1
    @38
    @2
    cprime
    eleq1
    @50
    @38
    @2
    @40
    @5
    cexp
    @50
    id
    @38
    @2
    cA
    cpc
    oveq1
    oveq12d
    ifbieq1d
    #
    fveq2d
    @44
    eqid
    @11
    clog
    fvex
    fvmpt
    syl
    #
    @0
    cA
    @34
    wcel
    cA
    elnnuz
    biimpi
    #
    @47
    @12
    @47
    @11
    @47
    @11
    @47
    @10
    @6
    c1
    cn
    @47
    @10
    wa
    #
    @2
    @5
    @47
    @29
    @10
    @49
    adantr
    @54
    @2
    cA
    @47
    @10
    simpr
    @0
    @18
    @10
    simpll
    pccld
    nnexpcld
    c1
    cn
    wcel
    @47
    @10
    wn
    wa
    1nn
    a1i
    ifclda
    nnrpd
    #
    relogcld
    recnd
    fsumser
    @0
    vp
    vm
    cmul
    caddc
    crp
    @45
    @44
    clog
    c1
    cA
    @37
    vm
    cv
    #
    crp
    wcel
    wa
    #
    @2
    @56
    cmul
    co
    #
    crp
    wcel
    @0
    @2
    @56
    rpmulcl
    adantl
    @47
    @2
    @45
    cfv
    #
    @11
    crp
    @47
    @29
    @59
    @11
    wceq
    @49
    vn
    @2
    @42
    @11
    cn
    @45
    @51
    @45
    eqid
    #
    @10
    @6
    c1
    @2
    @5
    cexp
    ovex
    1ex
    ifex
    fvmpt
    syl
    #
    @55
    eqeltrd
    @53
    @57
    @58
    clog
    cfv
    @14
    @56
    clog
    cfv
    caddc
    co
    wceq
    @0
    @2
    @56
    relogmul
    adantl
    @47
    @59
    clog
    cfv
    @12
    @48
    @47
    @59
    @11
    clog
    @61
    fveq2d
    @52
    eqtr4d
    seqhomo
    @0
    @46
    cA
    clog
    vn
    @45
    cA
    @60
    pcprod
    fveq2d
    3eqtr2d
    3eqtr3a
end
