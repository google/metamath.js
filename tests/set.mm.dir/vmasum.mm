include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cvma.mm"
include "cfv.mm"
include "csu.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cpc.mm"
include "cexp.mm"
include "clog.mm"
include "cmul.mm"
include "fveq2.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "ssrab2.mm"
include "a1i.mm"
include "inss1.mm"
include "sylancl.mm"
include "wa.mm"
include "cle.mm"
include "cz.mm"
include "wb.mm"
include "cn0.mm"
include "pccl.mm"
include "ancoms.mm"
include "nn0zd.mm"
include "fznn.mm"
include "syl.mm"
include "anbi2d.mm"
include "an12.mm"
include "prmz.mm"
include "adantl.mm"
include "iddvdsexp.mm"
include "sylan.mm"
include "wi.mm"
include "ad2antlr.mm"
include "prmnn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "syl2an.mm"
include "nnzd.mm"
include "nnz.mm"
include "ad2antrr.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "simpll.mm"
include "dvdsle.mm"
include "syld.mm"
include "baibd.mm"
include "sylibrd.mm"
include "pm4.71rd.mm"
include "breq1.mm"
include "elrab3.mm"
include "simplr.mm"
include "pcdvdsb.mm"
include "3bitr4rd.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitri.mm"
include "3bitr4g.mm"
include "cr.mm"
include "sselda.mm"
include "vmacl.mm"
include "recnd.mm"
include "cc0.mm"
include "wceq.mm"
include "simprr.mm"
include "fsumvma.mm"
include "chash.mm"
include "simprbi.mm"
include "elfznn.mm"
include "vmappw.mm"
include "sumeq2dv.mm"
include "cc.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "fsumconst.mm"
include "sylan2.mm"
include "hashfz1.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "pclogsum.mm"

theorem vmasum
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d p
  disjoint d x
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint p x
  disjoint A p
  assert |- ( A e. NN -> sum_ n e. { x e. NN | x || A } ( Lam ` n ) = ( log ` A ) )

  proof
    cA
    cn
    wcel
    #
    vx
    cv
    #
    cA
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vn
    cv
    #
    cvma
    cfv
    #
    vn
    csu
    c1
    cA
    cfz
    co
    #
    cprime
    cin
    #
    c1
    vp
    cv
    #
    cA
    cpc
    co
    #
    cfz
    co
    #
    @8
    vk
    cv
    #
    cexp
    co
    #
    cvma
    cfv
    #
    vk
    csu
    #
    vp
    csu
    @7
    @9
    @8
    clog
    cfv
    #
    cmul
    co
    #
    vp
    csu
    cA
    clog
    cfv
    @0
    vn
    @3
    @5
    @13
    @7
    vk
    @10
    vp
    @4
    @12
    cvma
    fveq2
    @0
    @6
    cfn
    wcel
    #
    @3
    @6
    wss
    @3
    cfn
    wcel
    @0
    c1
    cA
    fzfid
    #
    cA
    vx
    dvdsssfz1
    @6
    @3
    ssfi
    syl2anc
    @3
    cn
    wss
    @0
    @2
    vx
    cn
    ssrab2
    a1i
    #
    @0
    @17
    @7
    @6
    wss
    @7
    cfn
    wcel
    @18
    @6
    cprime
    inss1
    @6
    @7
    ssfi
    sylancl
    @0
    @8
    cprime
    wcel
    #
    @8
    @6
    wcel
    #
    @11
    @10
    wcel
    #
    wa
    #
    wa
    #
    @20
    @11
    cn
    wcel
    #
    @12
    @3
    wcel
    #
    wa
    #
    wa
    @8
    @7
    wcel
    #
    @22
    wa
    #
    @20
    @25
    wa
    @26
    wa
    @0
    @20
    @23
    @27
    @0
    @20
    wa
    #
    @23
    @21
    @25
    @11
    @9
    cle
    wbr
    #
    wa
    #
    wa
    #
    @27
    @30
    @22
    @32
    @21
    @30
    @9
    cz
    wcel
    @22
    @32
    wb
    @30
    @9
    @20
    @0
    @9
    cn0
    wcel
    #
    @8
    cA
    pccl
    ancoms
    #
    nn0zd
    @11
    @9
    fznn
    syl
    anbi2d
    @33
    @25
    @21
    @31
    wa
    #
    wa
    @30
    @27
    @21
    @25
    @31
    an12
    @30
    @25
    @36
    @26
    @30
    @25
    wa
    #
    @12
    cA
    cdvds
    wbr
    #
    @21
    @38
    wa
    @26
    @36
    @37
    @38
    @21
    @37
    @38
    @8
    cA
    cle
    wbr
    #
    @21
    @37
    @38
    @8
    cA
    cdvds
    wbr
    #
    @39
    @37
    @8
    @12
    cdvds
    wbr
    #
    @38
    @40
    @30
    @8
    cz
    wcel
    #
    @25
    @41
    @20
    @42
    @0
    @8
    prmz
    #
    adantl
    @8
    @11
    iddvdsexp
    sylan
    @37
    @42
    @12
    cz
    wcel
    cA
    cz
    wcel
    #
    @41
    @38
    wa
    @40
    wi
    @20
    @42
    @0
    @25
    @43
    ad2antlr
    #
    @37
    @12
    @30
    @8
    cn
    wcel
    #
    @11
    cn0
    wcel
    #
    @12
    cn
    wcel
    #
    @25
    @20
    @46
    @0
    @8
    prmnn
    #
    adantl
    @11
    nnnn0
    #
    @8
    @11
    nnexpcl
    syl2an
    #
    nnzd
    @0
    @44
    @20
    @25
    cA
    nnz
    ad2antrr
    #
    @8
    @12
    cA
    dvdstr
    syl3anc
    mpand
    @37
    @42
    @0
    @40
    @39
    wi
    @45
    @0
    @20
    @25
    simpll
    @8
    cA
    dvdsle
    syl2anc
    syld
    @37
    @44
    @46
    @21
    @39
    wb
    @52
    @20
    @46
    @0
    @25
    @49
    ad2antlr
    @44
    @21
    @46
    @39
    @8
    cA
    fznn
    baibd
    syl2anc
    sylibrd
    pm4.71rd
    @37
    @48
    @26
    @38
    wb
    @51
    @2
    @38
    vx
    @12
    cn
    @1
    @12
    cA
    cdvds
    breq1
    elrab3
    syl
    @37
    @31
    @38
    @21
    @37
    @20
    @44
    @47
    @31
    @38
    wb
    @0
    @20
    @25
    simplr
    @52
    @25
    @47
    @30
    @50
    adantl
    @11
    @8
    cA
    pcdvdsb
    syl3anc
    anbi2d
    3bitr4rd
    pm5.32da
    syl5bb
    bitrd
    pm5.32da
    @29
    @21
    @20
    wa
    #
    @22
    wa
    @21
    @20
    @22
    wa
    wa
    @24
    @28
    @53
    @22
    @8
    @6
    cprime
    elin
    #
    anbi1i
    @21
    @20
    @22
    anass
    @21
    @20
    @22
    an12
    3bitri
    @20
    @25
    @26
    anass
    3bitr4g
    @0
    @4
    @3
    wcel
    #
    wa
    #
    @5
    @56
    @4
    cn
    wcel
    @5
    cr
    wcel
    @0
    @3
    cn
    @4
    @19
    sselda
    @4
    vmacl
    syl
    recnd
    @0
    @55
    @5
    cc0
    wceq
    simprr
    fsumvma
    @0
    @7
    @14
    @16
    vp
    @0
    @28
    wa
    #
    @14
    @10
    @15
    vk
    csu
    #
    @10
    chash
    cfv
    #
    @15
    cmul
    co
    #
    @16
    @57
    @10
    @13
    @15
    vk
    @57
    @22
    wa
    @20
    @25
    @13
    @15
    wceq
    @28
    @20
    @0
    @22
    @28
    @21
    @20
    @54
    simprbi
    #
    ad2antlr
    @22
    @25
    @57
    @11
    @9
    elfznn
    adantl
    @8
    @11
    vmappw
    syl2anc
    sumeq2dv
    @57
    @10
    cfn
    wcel
    @15
    cc
    wcel
    @58
    @60
    wceq
    @57
    c1
    @9
    fzfid
    @57
    @15
    @57
    @8
    @57
    @8
    @28
    @46
    @0
    @28
    @20
    @46
    @61
    @49
    syl
    adantl
    nnrpd
    relogcld
    recnd
    @10
    @15
    vk
    fsumconst
    syl2anc
    @57
    @59
    @9
    @15
    cmul
    @57
    @34
    @59
    @9
    wceq
    @28
    @0
    @20
    @34
    @61
    @35
    sylan2
    @9
    hashfz1
    syl
    oveq1d
    3eqtrd
    sumeq2dv
    cA
    vp
    pclogsum
    3eqtrd
end
