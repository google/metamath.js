include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "c2.mm"
include "cfa.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "cz.mm"
include "wceq.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "sumex.mm"
include "fvmpt.mm"
include "oveq1d.mm"
include "fzfid.mm"
include "crp.mm"
include "2rp.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "syl.mm"
include "nnzd.mm"
include "rpexpcl.mm"
include "sylancr.mm"
include "rpcnd.mm"
include "wa.mm"
include "cneg.mm"
include "cc.mm"
include "elfznn.mm"
include "weq.mm"
include "fveq2.mm"
include "negeqd.mm"
include "oveq2d.mm"
include "ovex.mm"
include "adantl.mm"
include "nnnn0d.mm"
include "znegcld.mm"
include "eqeltrd.mm"
include "fsummulc1.mm"
include "caddc.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "2cnne0.mm"
include "expaddz.mm"
include "mpan.mm"
include "syl2anc.mm"
include "2z.mm"
include "cmin.mm"
include "zcnd.mm"
include "addcomd.mm"
include "nncnd.mm"
include "negsubd.mm"
include "eqtrd.mm"
include "cle.mm"
include "wbr.mm"
include "elfzle2.mm"
include "facwordi.mm"
include "syl3anc.mm"
include "wb.mm"
include "nn0sub.mm"
include "mpbid.mm"
include "zexpcl.mm"
include "eqeltrrd.mm"
include "fsumzcl.mm"

theorem aaliou3lem6
  let cA: class A
  let cF: class F
  let cH: class H
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  assume aaliou3lem.c: |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) )
  assume aaliou3lem.d: |- L = sum_ b e. NN ( F ` b )
  assume aaliou3lem.e: |- H = ( c e. NN |-> sum_ b e. ( 1 ... c ) ( F ` b ) )

  disjoint a b
  disjoint a c
  disjoint b c
  disjoint F b
  disjoint F c
  disjoint L c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a d
  disjoint a e
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint F d
  disjoint F e
  disjoint L d
  disjoint L e
  disjoint L f
  disjoint c f
  disjoint d f
  disjoint e f
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint A d
  disjoint A e
  assert |- ( A e. NN -> ( ( H ` A ) x. ( 2 ^ ( ! ` A ) ) ) e. ZZ )

  proof
    cA
    cn
    wcel
    #
    cA
    cH
    cfv
    #
    c2
    cA
    cfa
    cfv
    #
    cexp
    co
    #
    cmul
    co
    c1
    cA
    cfz
    co
    #
    vb
    cv
    #
    cF
    cfv
    #
    vb
    csu
    #
    @3
    cmul
    co
    #
    cz
    @0
    @1
    @7
    @3
    cmul
    vc
    cA
    c1
    vc
    cv
    #
    cfz
    co
    #
    @6
    vb
    csu
    @7
    cn
    cH
    @9
    cA
    wceq
    @10
    @4
    @6
    vb
    @9
    cA
    c1
    cfz
    oveq2
    sumeq1d
    aaliou3lem.e
    @4
    @6
    vb
    sumex
    fvmpt
    oveq1d
    @0
    @8
    @4
    @6
    @3
    cmul
    co
    #
    vb
    csu
    cz
    @0
    @4
    @6
    @3
    vb
    @0
    c1
    cA
    fzfid
    #
    @0
    @3
    @0
    c2
    crp
    wcel
    #
    @2
    cz
    wcel
    #
    @3
    crp
    wcel
    2rp
    @0
    @2
    @0
    cA
    cn0
    wcel
    #
    @2
    cn
    wcel
    #
    cA
    nnnn0
    #
    cA
    faccl
    #
    syl
    nnzd
    #
    c2
    @2
    rpexpcl
    sylancr
    rpcnd
    @0
    @5
    @4
    wcel
    #
    wa
    #
    @6
    c2
    @5
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    cc
    @20
    @6
    @24
    wceq
    #
    @0
    @20
    @5
    cn
    wcel
    #
    @25
    @5
    cA
    elfznn
    #
    va
    @5
    c2
    va
    cv
    #
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    @24
    cn
    cF
    va
    vb
    weq
    #
    @30
    @23
    c2
    cexp
    @31
    @29
    @22
    @28
    @5
    cfa
    fveq2
    negeqd
    oveq2d
    aaliou3lem.c
    c2
    @23
    cexp
    ovex
    fvmpt
    syl
    adantl
    #
    @21
    @24
    @21
    @13
    @23
    cz
    wcel
    #
    @24
    crp
    wcel
    2rp
    @21
    @22
    @21
    @22
    @21
    @5
    cn0
    wcel
    #
    @22
    cn
    wcel
    @21
    @5
    @20
    @26
    @0
    @27
    adantl
    nnnn0d
    #
    @5
    faccl
    syl
    #
    nnzd
    znegcld
    #
    c2
    @23
    rpexpcl
    sylancr
    rpcnd
    eqeltrd
    fsummulc1
    @0
    @4
    @11
    vb
    @12
    @21
    @11
    @24
    @3
    cmul
    co
    #
    cz
    @21
    @6
    @24
    @3
    cmul
    @32
    oveq1d
    @21
    c2
    @23
    @2
    caddc
    co
    #
    cexp
    co
    #
    @38
    cz
    @21
    @33
    @14
    @40
    @38
    wceq
    #
    @37
    @0
    @14
    @20
    @19
    adantr
    #
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    @33
    @14
    wa
    @41
    2cnne0
    c2
    @23
    @2
    expaddz
    mpan
    syl2anc
    @21
    c2
    cz
    wcel
    @39
    cn0
    wcel
    @40
    cz
    wcel
    2z
    @21
    @39
    @2
    @22
    cmin
    co
    #
    cn0
    @21
    @39
    @2
    @23
    caddc
    co
    @43
    @21
    @23
    @2
    @21
    @23
    @37
    zcnd
    @21
    @2
    @42
    zcnd
    #
    addcomd
    @21
    @2
    @22
    @44
    @21
    @22
    @36
    nncnd
    negsubd
    eqtrd
    @21
    @22
    @2
    cle
    wbr
    #
    @43
    cn0
    wcel
    #
    @21
    @34
    @15
    @5
    cA
    cle
    wbr
    #
    @45
    @35
    @0
    @15
    @20
    @17
    adantr
    #
    @20
    @47
    @0
    @5
    c1
    cA
    elfzle2
    adantl
    @5
    cA
    facwordi
    syl3anc
    @21
    @22
    cn0
    wcel
    @2
    cn0
    wcel
    @45
    @46
    wb
    @21
    @22
    @36
    nnnn0d
    @21
    @2
    @21
    @15
    @16
    @48
    @18
    syl
    nnnn0d
    @22
    @2
    nn0sub
    syl2anc
    mpbid
    eqeltrd
    c2
    @39
    zexpcl
    sylancr
    eqeltrrd
    eqeltrd
    fsumzcl
    eqeltrd
    eqeltrd
end
