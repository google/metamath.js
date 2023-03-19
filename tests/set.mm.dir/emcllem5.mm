include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cdiv.mm"
include "csu.mm"
include "caddc.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "cmpt.mm"
include "cseq.mm"
include "wcel.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "nncnd.mm"
include "1cnd.mm"
include "nnne0d.mm"
include "divdird.mm"
include "dividd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "peano2nn.mm"
include "syl.mm"
include "nnrpd.mm"
include "relogdivd.mm"
include "eqtr3d.mm"
include "sumeq2dv.mm"
include "fveq2.mm"
include "nnz.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "relogcld.mm"
include "recnd.mm"
include "telfsum2.mm"
include "cc0.mm"
include "log1.mm"
include "oveq2i.mm"
include "subid1d.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "fzfid.mm"
include "nnrecred.mm"
include "crp.mm"
include "1rp.mm"
include "rpreccld.mm"
include "rpaddcl.mm"
include "sylancr.mm"
include "fsumsub.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "id.mm"
include "resubcld.mm"
include "fsumser.mm"
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

theorem emcllem5
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  let cN: class N
  assume emcl.1: |- F = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` n ) ) )
  assume emcl.2: |- G = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` ( n + 1 ) ) ) )
  assume emcl.3: |- H = ( n e. NN |-> ( log ` ( 1 + ( 1 / n ) ) ) )
  assume emcl.4: |- T = ( n e. NN |-> ( ( 1 / n ) - ( log ` ( 1 + ( 1 / n ) ) ) ) )

  disjoint H m
  disjoint m n
  disjoint T m
  disjoint T n
  disjoint i k
  disjoint i x
  disjoint F i
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G i
  disjoint G k
  disjoint G x
  disjoint k m
  disjoint H k
  disjoint N m
  disjoint N n
  disjoint k n
  disjoint T k
  disjoint m x
  disjoint n x
  disjoint T x
  assert |- G = seq 1 ( + , T )

  proof
    vn
    cn
    c1
    vn
    cv
    #
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    @0
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    vn
    cn
    @0
    caddc
    cT
    c1
    cseq
    #
    cfv
    #
    cmpt
    #
    cG
    @8
    vn
    cn
    @7
    @9
    @0
    cn
    wcel
    #
    @4
    @1
    c1
    @3
    caddc
    co
    #
    clog
    cfv
    #
    vm
    csu
    #
    cmin
    co
    #
    @7
    @9
    @11
    @14
    @6
    @4
    cmin
    @11
    @14
    @1
    @2
    c1
    caddc
    co
    #
    clog
    cfv
    #
    @2
    clog
    cfv
    #
    cmin
    co
    #
    vm
    csu
    @6
    c1
    clog
    cfv
    #
    cmin
    co
    #
    @6
    @11
    @1
    @13
    @19
    vm
    @11
    @2
    @1
    wcel
    #
    wa
    #
    @16
    @2
    cdiv
    co
    #
    clog
    cfv
    @13
    @19
    @23
    @24
    @12
    clog
    @23
    @24
    @2
    @2
    cdiv
    co
    #
    @3
    caddc
    co
    @12
    @23
    @2
    c1
    @2
    @23
    @2
    @22
    @2
    cn
    wcel
    #
    @11
    @2
    @0
    elfznn
    adantl
    #
    nncnd
    #
    @23
    1cnd
    @28
    @23
    @2
    @27
    nnne0d
    #
    divdird
    @23
    @25
    c1
    @3
    caddc
    @23
    @2
    @28
    @29
    dividd
    oveq1d
    eqtrd
    fveq2d
    @23
    @16
    @2
    @23
    @16
    @23
    @26
    @16
    cn
    wcel
    @27
    @2
    peano2nn
    syl
    nnrpd
    @23
    @2
    @27
    nnrpd
    #
    relogdivd
    eqtr3d
    sumeq2dv
    @11
    vx
    cv
    #
    clog
    cfv
    #
    @18
    @17
    @20
    vm
    vx
    @6
    c1
    @0
    @31
    @2
    clog
    fveq2
    @31
    @16
    clog
    fveq2
    @31
    c1
    clog
    fveq2
    @31
    @5
    clog
    fveq2
    @0
    nnz
    @11
    @5
    cn
    c1
    cuz
    cfv
    #
    @0
    peano2nn
    #
    nnuz
    syl6eleq
    @11
    @31
    c1
    @5
    cfz
    co
    wcel
    #
    wa
    #
    @32
    @36
    @31
    @36
    @31
    @35
    @31
    cn
    wcel
    @11
    @31
    @5
    elfznn
    adantl
    nnrpd
    relogcld
    recnd
    telfsum2
    @11
    @21
    @6
    cc0
    cmin
    co
    @6
    @20
    cc0
    @6
    cmin
    log1
    oveq2i
    @11
    @6
    @11
    @6
    @11
    @5
    @11
    @5
    @34
    nnrpd
    relogcld
    recnd
    subid1d
    syl5eq
    3eqtrd
    oveq2d
    @11
    @1
    @3
    @13
    cmin
    co
    #
    vm
    csu
    @15
    @9
    @11
    @1
    @3
    @13
    vm
    @11
    c1
    @0
    fzfid
    @23
    @3
    @23
    @2
    @27
    nnrecred
    #
    recnd
    @23
    @13
    @23
    @12
    @23
    c1
    crp
    wcel
    @3
    crp
    wcel
    @12
    crp
    wcel
    1rp
    @23
    @2
    @30
    rpreccld
    c1
    @3
    rpaddcl
    sylancr
    relogcld
    #
    recnd
    fsumsub
    @11
    @37
    vm
    cT
    c1
    @0
    @23
    @26
    @2
    cT
    cfv
    @37
    wceq
    @27
    vn
    @2
    c1
    @0
    cdiv
    co
    #
    c1
    @40
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    @37
    cn
    cT
    @0
    @2
    wceq
    #
    @40
    @3
    @42
    @13
    cmin
    @0
    @2
    c1
    cdiv
    oveq2
    #
    @43
    @41
    @12
    clog
    @43
    @40
    @3
    c1
    caddc
    @44
    oveq2d
    fveq2d
    oveq12d
    emcl.4
    @3
    @13
    cmin
    ovex
    fvmpt
    syl
    @11
    @0
    cn
    @33
    @11
    id
    nnuz
    syl6eleq
    @23
    @37
    @23
    @3
    @13
    @38
    @39
    resubcld
    recnd
    fsumser
    eqtr3d
    eqtr3d
    mpteq2ia
    emcl.2
    @8
    cn
    wfn
    #
    @8
    @10
    wceq
    @45
    @8
    @33
    wfn
    #
    c1
    cz
    wcel
    @46
    1z
    caddc
    cT
    c1
    seqfn
    ax-mp
    cn
    @33
    @8
    nnuz
    fneq2i
    mpbir
    vn
    cn
    @8
    dffn5
    mpbi
    3eqtr4i
end
