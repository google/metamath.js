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
include "binom2sub1.mm"
include "2cnd.mm"
include "mulcld.mm"
include "a1i.mm"
include "subsubd.mm"
include "eqtr4d.mm"
include "1red.mm"
include "cr.mm"
include "2re.mm"
include "eluzelre.mm"
include "remulcld.mm"
include "resubcld.mm"
include "nnred.mm"
include "eluz2gt1.mm"
include "lt2addmuld.mm"
include "remulcl.mm"
include "sylancr.mm"
include "ltaddsubd.mm"
include "mpbid.mm"
include "ltsub2dd.mm"
include "eqbrtrd.mm"
include "ltm1d.mm"
include "npcan.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "nonsq.mm"
include "syl22anc.mm"
include "eldifd.mm"

theorem rmspecsqrtnq
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
    cmul
    co
    #
    c1
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
    @15
    cmin
    co
    c1
    caddc
    co
    #
    @17
    @0
    cA
    cc
    wcel
    #
    @10
    @18
    wceq
    @5
    cA
    binom2sub1
    syl
    @0
    @1
    @15
    c1
    @6
    @0
    c2
    cA
    @0
    2cnd
    @5
    mulcld
    @4
    @0
    ax-1cn
    a1i
    subsubd
    eqtr4d
    @0
    c1
    @16
    @1
    @0
    1red
    #
    @0
    @15
    c1
    @0
    c2
    cA
    c2
    cr
    wcel
    #
    @0
    2re
    a1i
    c2
    cA
    eluzelre
    #
    remulcld
    @20
    resubcld
    @0
    @1
    @14
    nnred
    #
    @0
    c1
    c1
    caddc
    co
    @15
    clt
    wbr
    c1
    @16
    clt
    wbr
    @0
    c1
    c1
    cA
    @20
    @20
    @22
    cA
    eluz2gt1
    #
    @24
    lt2addmuld
    @0
    c1
    c1
    @15
    @20
    @20
    @0
    @21
    cA
    cr
    wcel
    @15
    cr
    wcel
    2re
    @22
    c2
    cA
    remulcl
    sylancr
    ltaddsubd
    mpbid
    ltsub2dd
    eqbrtrd
    @0
    @2
    @1
    @12
    clt
    @0
    @1
    @23
    ltm1d
    @0
    @11
    cA
    c2
    cexp
    @0
    @19
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
