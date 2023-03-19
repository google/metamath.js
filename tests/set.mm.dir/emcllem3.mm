include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "clog.mm"
include "cfv.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "cmin.mm"
include "peano2nn.mm"
include "nnrpd.mm"
include "nnrp.mm"
include "relogdivd.mm"
include "nncn.mm"
include "1cnd.mm"
include "nnne0.mm"
include "divdird.mm"
include "dividd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "fzfid.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrecred.mm"
include "fsumrecl.mm"
include "recnd.mm"
include "relogcld.mm"
include "nnncan1d.mm"
include "3eqtr4d.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "sumeq1d.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "oveq1.mm"

theorem emcllem3
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  let cT: class T
  assume emcl.1: |- F = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` n ) ) )
  assume emcl.2: |- G = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` ( n + 1 ) ) ) )
  assume emcl.3: |- H = ( n e. NN |-> ( log ` ( 1 + ( 1 / n ) ) ) )

  disjoint H m
  disjoint m n
  disjoint N m
  disjoint N n
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
  disjoint k n
  disjoint T k
  disjoint m x
  disjoint T m
  disjoint n x
  disjoint T n
  disjoint T x
  assert |- ( N e. NN -> ( H ` N ) = ( ( F ` N ) - ( G ` N ) ) )

  proof
    cN
    cn
    wcel
    #
    c1
    c1
    cN
    cdiv
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    c1
    cN
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
    cN
    clog
    cfv
    #
    cmin
    co
    #
    @7
    cN
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
    cmin
    co
    #
    cN
    cH
    cfv
    cN
    cF
    cfv
    #
    cN
    cG
    cfv
    #
    cmin
    co
    @0
    @10
    cN
    cdiv
    co
    #
    clog
    cfv
    @11
    @8
    cmin
    co
    @3
    @13
    @0
    @10
    cN
    @0
    @10
    cN
    peano2nn
    nnrpd
    #
    cN
    nnrp
    #
    relogdivd
    @0
    @2
    @16
    clog
    @0
    @16
    cN
    cN
    cdiv
    co
    #
    @1
    caddc
    co
    @2
    @0
    cN
    c1
    cN
    cN
    nncn
    #
    @0
    1cnd
    @20
    cN
    nnne0
    #
    divdird
    @0
    @19
    c1
    @1
    caddc
    @0
    cN
    @20
    @21
    dividd
    oveq1d
    eqtr2d
    fveq2d
    @0
    @7
    @8
    @11
    @0
    @7
    @0
    @4
    @6
    vm
    @0
    c1
    cN
    fzfid
    @0
    @5
    @4
    wcel
    #
    wa
    @5
    @22
    @5
    cn
    wcel
    @0
    @5
    cN
    elfznn
    adantl
    nnrecred
    fsumrecl
    recnd
    @0
    @8
    @0
    cN
    @18
    relogcld
    recnd
    @0
    @11
    @0
    @10
    @17
    relogcld
    recnd
    nnncan1d
    3eqtr4d
    vn
    cN
    c1
    c1
    vn
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    clog
    cfv
    @3
    cn
    cH
    @23
    cN
    wceq
    #
    @25
    @2
    clog
    @26
    @24
    @1
    c1
    caddc
    @23
    cN
    c1
    cdiv
    oveq2
    oveq2d
    fveq2d
    emcl.3
    @2
    clog
    fvex
    fvmpt
    @0
    @14
    @9
    @15
    @12
    cmin
    vn
    cN
    c1
    @23
    cfz
    co
    #
    @6
    vm
    csu
    #
    @23
    clog
    cfv
    #
    cmin
    co
    @9
    cn
    cF
    @26
    @28
    @7
    @29
    @8
    cmin
    @26
    @27
    @4
    @6
    vm
    @23
    cN
    c1
    cfz
    oveq2
    sumeq1d
    #
    @23
    cN
    clog
    fveq2
    oveq12d
    emcl.1
    @7
    @8
    cmin
    ovex
    fvmpt
    vn
    cN
    @28
    @23
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    @12
    cn
    cG
    @26
    @28
    @7
    @32
    @11
    cmin
    @30
    @26
    @31
    @10
    clog
    @23
    cN
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    emcl.2
    @7
    @11
    cmin
    ovex
    fvmpt
    oveq12d
    3eqtr4d
end
