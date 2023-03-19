include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "cc.mm"
include "cq.mm"
include "eluzelcn.mm"
include "sqcld.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "sqrtcld.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "wn.mm"
include "cn.mm"
include "eluz2nn.mm"
include "nnsqcld.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "cmul.mm"
include "wceq.mm"
include "binom2sub.mm"
include "cr.mm"
include "2re.mm"
include "eluzelre.mm"
include "1re.mm"
include "remulcl.mm"
include "sylancr.mm"
include "recnd.mm"
include "resqcli.mm"
include "recni.mm"
include "a1i.mm"
include "subsubd.mm"
include "eqtr4d.mm"
include "resubcl.mm"
include "nnred.mm"
include "2timesi.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "cc0.mm"
include "wb.mm"
include "2pos.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "ltaddsubd.mm"
include "mulid1d.mm"
include "oveq2d.mm"
include "sq1.mm"
include "oveq12d.mm"
include "breqtrrd.mm"
include "ltsub2dd.mm"
include "eqbrtrd.mm"
include "ltm1d.mm"
include "npcan.mm"
include "oveq1d.mm"
include "nonsq.mm"
include "syl22anc.mm"
include "eldifd.mm"

theorem rmspecsqrtnqOLD
  let cA: class A


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( sqrt ` ( ( A ^ 2 ) - 1 ) ) e. ( CC \ QQ ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cA
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    cc
    cq
    @0
    @2
    @0
    @1
    cc
    wcel
    c1
    cc
    wcel
    #
    @2
    cc
    wcel
    @0
    cA
    c2
    cA
    eluzelcn
    #
    sqcld
    #
    ax-1cn
    @1
    c1
    subcl
    sylancl
    sqrtcld
    @0
    @2
    cn0
    wcel
    #
    cA
    c1
    cmin
    co
    #
    cn0
    wcel
    #
    @8
    c2
    cexp
    co
    #
    @2
    clt
    wbr
    @2
    @8
    c1
    caddc
    co
    #
    c2
    cexp
    co
    #
    clt
    wbr
    @3
    cq
    wcel
    wn
    @0
    @1
    cn
    wcel
    @7
    @0
    cA
    cA
    eluz2nn
    #
    nnsqcld
    #
    @1
    nnm1nn0
    syl
    @0
    cA
    cn
    wcel
    #
    @9
    @13
    cA
    nnm1nn0
    syl
    @0
    @10
    @1
    c2
    cA
    c1
    cmul
    co
    #
    cmul
    co
    #
    c1
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmin
    co
    #
    @2
    clt
    @0
    @10
    @1
    @17
    cmin
    co
    @18
    caddc
    co
    #
    @20
    @0
    cA
    cc
    wcel
    #
    @4
    @10
    @21
    wceq
    @5
    ax-1cn
    cA
    c1
    binom2sub
    sylancl
    @0
    @1
    @17
    @18
    @6
    @0
    @17
    @0
    c2
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @17
    cr
    wcel
    #
    2re
    @0
    cA
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @24
    c2
    cA
    eluzelre
    #
    1re
    cA
    c1
    remulcl
    sylancl
    c2
    @16
    remulcl
    sylancr
    #
    recnd
    @18
    cc
    wcel
    @0
    @18
    c1
    1re
    resqcli
    #
    recni
    a1i
    subsubd
    eqtr4d
    @0
    c1
    @19
    @1
    @27
    @0
    1re
    a1i
    #
    @0
    @25
    @18
    cr
    wcel
    @19
    cr
    wcel
    @29
    @30
    @17
    @18
    resubcl
    sylancl
    @0
    @1
    @14
    nnred
    #
    @0
    c1
    c2
    cA
    cmul
    co
    #
    c1
    cmin
    co
    #
    @19
    clt
    @0
    c1
    c1
    caddc
    co
    #
    @33
    clt
    wbr
    c1
    @34
    clt
    wbr
    @0
    @35
    c2
    c1
    cmul
    co
    #
    @33
    clt
    c1
    ax-1cn
    2timesi
    @0
    c1
    cA
    clt
    wbr
    #
    @36
    @33
    clt
    wbr
    #
    @0
    @15
    @37
    cA
    eluz2b2
    simprbi
    @0
    @27
    @26
    @23
    cc0
    c2
    clt
    wbr
    #
    @37
    @38
    wb
    @31
    @28
    @23
    @0
    2re
    a1i
    @39
    @0
    2pos
    a1i
    c1
    cA
    c2
    ltmul2
    syl112anc
    mpbid
    syl5eqbrr
    @0
    c1
    c1
    @33
    @31
    @31
    @0
    @23
    @26
    @33
    cr
    wcel
    2re
    @28
    c2
    cA
    remulcl
    sylancr
    ltaddsubd
    mpbid
    @0
    @17
    @33
    @18
    c1
    cmin
    @0
    @16
    cA
    c2
    cmul
    @0
    cA
    @5
    mulid1d
    oveq2d
    @18
    c1
    wceq
    @0
    sq1
    a1i
    oveq12d
    breqtrrd
    ltsub2dd
    eqbrtrd
    @0
    @2
    @1
    @12
    clt
    @0
    @1
    @32
    ltm1d
    @0
    @11
    cA
    c2
    cexp
    @0
    @22
    @4
    @11
    cA
    wceq
    @5
    ax-1cn
    cA
    c1
    npcan
    sylancl
    oveq1d
    breqtrrd
    @2
    @8
    nonsq
    syl22anc
    eldifd
end
