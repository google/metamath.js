include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "caddc.mm"
include "cn.mm"
include "cv.mm"
include "cprime.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "wceq.mm"
include "eleq1.mm"
include "oveq2.mm"
include "ifbieq1d.mm"
include "cbvmptv.mm"
include "prmreclem6.mm"
include "cfz.mm"
include "cin.mm"
include "csu.mm"
include "cfv.mm"
include "wss.mm"
include "cc.mm"
include "wral.mm"
include "wa.mm"
include "cuz.mm"
include "cfn.mm"
include "wo.mm"
include "inss2.mm"
include "sseli.mm"
include "elfznn.mm"
include "nnrecre.mm"
include "recnd.mm"
include "3syl.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "fzfi.mm"
include "olci.mm"
include "sumss2.mm"
include "mp2an.mm"
include "elin.mm"
include "rbaib.mm"
include "ifbid.mm"
include "sumeq2i.mm"
include "eqtri.mm"
include "adantl.mm"
include "wtru.mm"
include "prmnn.mm"
include "syl.mm"
include "wn.mm"
include "0cnd.mm"
include "ifclda.mm"
include "trud.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "id.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "a1i.mm"
include "fsumser.mm"
include "syl5eq.mm"
include "mpteq2ia.mm"
include "wfn.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "ax-mp.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "dffn5.mm"
include "mpbi.mm"
include "3eqtr4i.mm"
include "eleq1i.mm"
include "mtbir.mm"

theorem prmrec
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vm: setvar m
  assume prmrec.f: |- F = ( n e. NN |-> sum_ k e. ( Prime i^i ( 1 ... n ) ) ( 1 / k ) )

  disjoint k n
  disjoint k m
  disjoint m n
  assert |- -. F e. dom ~~>

  proof
    cF
    cli
    cdm
    #
    wcel
    caddc
    vm
    cn
    vm
    cv
    #
    cprime
    wcel
    #
    c1
    @1
    cdiv
    co
    #
    cc0
    cif
    #
    cmpt
    #
    c1
    cseq
    #
    @0
    wcel
    vk
    @5
    vm
    vk
    cn
    @4
    vk
    cv
    #
    cprime
    wcel
    #
    c1
    @7
    cdiv
    co
    #
    cc0
    cif
    #
    @1
    @7
    wceq
    @2
    @8
    @3
    @9
    cc0
    @1
    @7
    cprime
    eleq1
    @1
    @7
    c1
    cdiv
    oveq2
    ifbieq1d
    cbvmptv
    #
    prmreclem6
    cF
    @6
    @0
    vn
    cn
    cprime
    c1
    vn
    cv
    #
    cfz
    co
    #
    cin
    #
    @9
    vk
    csu
    #
    cmpt
    vn
    cn
    @12
    @6
    cfv
    #
    cmpt
    #
    cF
    @6
    vn
    cn
    @15
    @16
    @12
    cn
    wcel
    #
    @15
    @13
    @10
    vk
    csu
    #
    @16
    @15
    @13
    @7
    @14
    wcel
    #
    @9
    cc0
    cif
    #
    vk
    csu
    #
    @19
    @14
    @13
    wss
    #
    @9
    cc
    wcel
    #
    vk
    @14
    wral
    #
    wa
    @13
    c1
    cuz
    cfv
    #
    wss
    #
    @13
    cfn
    wcel
    #
    wo
    @15
    @22
    wceq
    @23
    @25
    cprime
    @13
    inss2
    #
    @24
    vk
    @14
    @20
    @7
    @13
    wcel
    #
    @7
    cn
    wcel
    #
    @24
    @14
    @13
    @7
    @29
    sseli
    @7
    @12
    elfznn
    #
    @31
    @9
    @7
    nnrecre
    recnd
    #
    3syl
    rgen
    pm3.2i
    @28
    @27
    c1
    @12
    fzfi
    olci
    @14
    @13
    @9
    vk
    c1
    sumss2
    mp2an
    @13
    @21
    @10
    vk
    @30
    @20
    @8
    @9
    cc0
    @20
    @8
    @30
    @7
    cprime
    @13
    elin
    rbaib
    ifbid
    sumeq2i
    eqtri
    @18
    @10
    vk
    @5
    c1
    @12
    @18
    @30
    wa
    #
    @31
    @10
    cc
    wcel
    #
    @7
    @5
    cfv
    @10
    wceq
    @30
    @31
    @18
    @32
    adantl
    @35
    wtru
    @8
    @9
    cc0
    cc
    @8
    @24
    wtru
    @8
    @31
    @24
    @7
    prmnn
    @33
    syl
    adantl
    wtru
    @8
    wn
    wa
    0cnd
    ifclda
    trud
    #
    vk
    cn
    @10
    cc
    @5
    @11
    fvmpt2
    sylancl
    @18
    @12
    cn
    @26
    @18
    id
    nnuz
    syl6eleq
    @35
    @34
    @36
    a1i
    fsumser
    syl5eq
    mpteq2ia
    prmrec.f
    @6
    cn
    wfn
    #
    @6
    @17
    wceq
    @37
    @6
    @26
    wfn
    #
    c1
    cz
    wcel
    @38
    1z
    caddc
    @5
    c1
    seqfn
    ax-mp
    cn
    @26
    @6
    nnuz
    fneq2i
    mpbir
    vn
    cn
    @6
    dffn5
    mpbi
    3eqtr4i
    eleq1i
    mtbir
end
