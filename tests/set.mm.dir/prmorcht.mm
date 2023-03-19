include "cn.mm"
include "wcel.mm"
include "ccht.mm"
include "cfv.mm"
include "ce.mm"
include "caddc.mm"
include "cv.mm"
include "cprime.mm"
include "clog.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "cmul.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "cin.mm"
include "cicc.mm"
include "cr.mm"
include "wceq.mm"
include "nnre.mm"
include "chtval.mm"
include "syl.mm"
include "cfl.mm"
include "c2.mm"
include "cuz.mm"
include "2eluzge1.mm"
include "ppisval2.mm"
include "sylancl.mm"
include "cz.mm"
include "nnz.mm"
include "flid.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "sumeq1d.mm"
include "wss.mm"
include "cc.mm"
include "wral.mm"
include "inss1.mm"
include "sseli.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "recnd.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "cfn.mm"
include "wo.mm"
include "fzfi.mm"
include "olci.mm"
include "sumss2.mm"
include "mpan2.mm"
include "sylancr.mm"
include "elin.mm"
include "baibr.mm"
include "ifbid.mm"
include "sumeq2i.mm"
include "syl6eqr.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "0cn.mm"
include "elexi.mm"
include "ifex.mm"
include "fvmpt.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "ifcl.mm"
include "fsumser.mm"
include "fveq2d.mm"
include "addcl.mm"
include "eqeltrd.mm"
include "efadd.mm"
include "1nn.mm"
include "reeflogd.mm"
include "fvif.mm"
include "log1.mm"
include "ifeq2.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "id.mm"
include "vex.mm"
include "3eqtr4d.mm"
include "seqhomo.mm"

theorem prmorcht
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vp: setvar p
  assume prmorcht.1: |- F = ( n e. NN |-> if ( n e. Prime , n , 1 ) )


  assert |- ( A e. NN -> ( exp ` ( theta ` A ) ) = ( seq 1 ( x. , F ) ` A ) )

  proof
    cA
    cn
    wcel
    #
    cA
    ccht
    cfv
    #
    ce
    cfv
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
    @2
    clog
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    c1
    cseq
    cfv
    #
    ce
    cfv
    cA
    cmul
    cF
    c1
    cseq
    cfv
    @0
    @1
    @7
    ce
    @0
    @1
    c1
    cA
    cfz
    co
    #
    vk
    cv
    #
    cprime
    wcel
    #
    @9
    clog
    cfv
    #
    cc0
    cif
    #
    vk
    csu
    #
    @7
    @0
    @1
    @8
    @9
    @8
    cprime
    cin
    #
    wcel
    #
    @11
    cc0
    cif
    #
    vk
    csu
    #
    @13
    @0
    @1
    cc0
    cA
    cicc
    co
    cprime
    cin
    #
    @11
    vk
    csu
    #
    @17
    @0
    cA
    cr
    wcel
    #
    @1
    @19
    wceq
    cA
    nnre
    #
    cA
    vk
    chtval
    syl
    @0
    @19
    @14
    @11
    vk
    csu
    #
    @17
    @0
    @18
    @14
    @11
    vk
    @0
    @18
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    @14
    @0
    @20
    c2
    c1
    cuz
    cfv
    #
    wcel
    @18
    @25
    wceq
    @21
    2eluzge1
    cA
    c1
    ppisval2
    sylancl
    @0
    @24
    @8
    cprime
    @0
    @23
    cA
    c1
    cfz
    @0
    cA
    cz
    wcel
    @23
    cA
    wceq
    cA
    nnz
    cA
    flid
    syl
    oveq2d
    ineq1d
    eqtrd
    sumeq1d
    @0
    @14
    @8
    wss
    #
    @11
    cc
    wcel
    #
    vk
    @14
    wral
    #
    @22
    @17
    wceq
    #
    @8
    cprime
    inss1
    #
    @0
    @28
    vk
    @14
    @15
    @0
    @9
    @8
    wcel
    #
    @28
    @14
    @8
    @9
    @31
    sseli
    @0
    @32
    wa
    #
    @11
    @33
    @9
    @33
    @9
    @32
    @9
    cn
    wcel
    #
    @0
    @9
    cA
    elfznn
    adantl
    #
    nnrpd
    relogcld
    recnd
    #
    sylan2
    ralrimiva
    @27
    @29
    wa
    @8
    @26
    wss
    #
    @8
    cfn
    wcel
    #
    wo
    @30
    @38
    @37
    c1
    cA
    fzfi
    olci
    @14
    @8
    @11
    vk
    c1
    sumss2
    mpan2
    sylancr
    eqtrd
    eqtrd
    @8
    @12
    @16
    vk
    @32
    @10
    @15
    @11
    cc0
    @15
    @32
    @10
    @9
    @8
    cprime
    elin
    baibr
    ifbid
    sumeq2i
    syl6eqr
    @0
    @12
    vk
    @6
    c1
    cA
    @33
    @34
    @9
    @6
    cfv
    #
    @12
    wceq
    @35
    vn
    @9
    @5
    @12
    cn
    @6
    @2
    @9
    wceq
    #
    @3
    @10
    @4
    @11
    cc0
    @2
    @9
    cprime
    eleq1
    #
    @2
    @9
    clog
    fveq2
    ifbieq1d
    @6
    eqid
    @10
    @11
    cc0
    @9
    clog
    fvex
    cc0
    cc
    0cn
    elexi
    ifex
    fvmpt
    syl
    #
    @0
    cA
    @26
    wcel
    cA
    elnnuz
    biimpi
    #
    @33
    @28
    cc0
    cc
    wcel
    @12
    cc
    wcel
    @36
    0cn
    @10
    @11
    cc0
    cc
    ifcl
    sylancl
    #
    fsumser
    eqtrd
    fveq2d
    @0
    vk
    vp
    caddc
    cmul
    cc
    @6
    cF
    ce
    c1
    cA
    @9
    cc
    wcel
    vp
    cv
    #
    cc
    wcel
    wa
    #
    @9
    @45
    caddc
    co
    #
    cc
    wcel
    @0
    @9
    @45
    addcl
    adantl
    @33
    @39
    @12
    cc
    @42
    @44
    eqeltrd
    @43
    @46
    @47
    ce
    cfv
    @9
    ce
    cfv
    @45
    ce
    cfv
    cmul
    co
    wceq
    @0
    @9
    @45
    efadd
    adantl
    @33
    @10
    @9
    c1
    cif
    #
    clog
    cfv
    #
    ce
    cfv
    @48
    @39
    ce
    cfv
    @9
    cF
    cfv
    #
    @33
    @48
    @33
    @48
    @33
    @34
    c1
    cn
    wcel
    @48
    cn
    wcel
    @35
    1nn
    @10
    @9
    c1
    cn
    ifcl
    sylancl
    nnrpd
    reeflogd
    @33
    @39
    @49
    ce
    @33
    @39
    @12
    @49
    @42
    @49
    @10
    @11
    c1
    clog
    cfv
    #
    cif
    #
    @12
    @10
    @9
    c1
    clog
    fvif
    @51
    cc0
    wceq
    @52
    @12
    wceq
    log1
    @10
    @51
    cc0
    @11
    ifeq2
    ax-mp
    eqtri
    syl6eqr
    fveq2d
    @33
    @34
    @50
    @48
    wceq
    @35
    vn
    @9
    @3
    @2
    c1
    cif
    @48
    cn
    cF
    @40
    @3
    @10
    @2
    @9
    c1
    @41
    @40
    id
    ifbieq1d
    prmorcht.1
    @10
    @9
    c1
    vk
    vex
    c1
    cn
    1nn
    elexi
    ifex
    fvmpt
    syl
    3eqtr4d
    seqhomo
    eqtrd
end
