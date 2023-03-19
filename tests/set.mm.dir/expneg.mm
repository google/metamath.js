include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "elnn0.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cfv.mm"
include "cif.mm"
include "wne.mm"
include "wn.mm"
include "nnne0.mm"
include "adantl.mm"
include "nncn.mm"
include "negeq0d.mm"
include "necon3abid.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "nnnn0.mm"
include "nn0nlt0.mm"
include "syl.mm"
include "nn0red.mm"
include "lt0neg1d.mm"
include "mtbid.mm"
include "negnegd.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cz.mm"
include "nnnegz.mm"
include "expval.mm"
include "sylan2.mm"
include "expnnval.mm"
include "3eqtr4d.mm"
include "1div1e1.mm"
include "eqcomi.mm"
include "negeq.mm"
include "neg0.mm"
include "syl6eq.mm"
include "exp0.mm"
include "sylan9eqr.mm"
include "oveq2.mm"
include "3eqtr4a.mm"
include "jaodan.mm"
include "sylan2b.mm"

theorem expneg
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( A ^ -u N ) = ( 1 / ( A ^ N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cc
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cA
    cN
    cneg
    #
    cexp
    co
    #
    c1
    cA
    cN
    cexp
    co
    #
    cdiv
    co
    #
    wceq
    #
    cN
    elnn0
    @1
    @2
    @8
    @3
    @1
    @2
    wa
    #
    @4
    cc0
    wceq
    #
    c1
    cc0
    @4
    clt
    wbr
    #
    @4
    cmul
    cn
    cA
    csn
    cxp
    c1
    cseq
    #
    cfv
    #
    c1
    @4
    cneg
    #
    @12
    cfv
    #
    cdiv
    co
    #
    cif
    #
    cif
    #
    c1
    cN
    @12
    cfv
    #
    cdiv
    co
    #
    @5
    @7
    @9
    @18
    @17
    @16
    @20
    @9
    @10
    c1
    @17
    @9
    cN
    cc0
    wne
    #
    @10
    wn
    @2
    @21
    @1
    cN
    nnne0
    adantl
    @9
    @10
    cN
    cc0
    @9
    cN
    @2
    cN
    cc
    wcel
    @1
    cN
    nncn
    adantl
    #
    negeq0d
    necon3abid
    mpbid
    iffalsed
    @9
    @11
    @13
    @16
    @9
    cN
    cc0
    clt
    wbr
    #
    @11
    @9
    @0
    @23
    wn
    @2
    @0
    @1
    cN
    nnnn0
    adantl
    #
    cN
    nn0nlt0
    syl
    @9
    cN
    @9
    cN
    @24
    nn0red
    lt0neg1d
    mtbid
    iffalsed
    @9
    @15
    @19
    c1
    cdiv
    @9
    @14
    cN
    @12
    @9
    cN
    @22
    negnegd
    fveq2d
    oveq2d
    3eqtrd
    @2
    @1
    @4
    cz
    wcel
    @5
    @18
    wceq
    cN
    nnnegz
    cA
    @4
    expval
    sylan2
    @9
    @6
    @19
    c1
    cdiv
    cA
    cN
    expnnval
    oveq2d
    3eqtr4d
    @1
    @3
    wa
    #
    c1
    c1
    c1
    cdiv
    co
    #
    @5
    @7
    @26
    c1
    1div1e1
    eqcomi
    @3
    @1
    @5
    cA
    cc0
    cexp
    co
    #
    c1
    @3
    @4
    cc0
    cA
    cexp
    @3
    @4
    cc0
    cneg
    cc0
    cN
    cc0
    negeq
    neg0
    syl6eq
    oveq2d
    cA
    exp0
    #
    sylan9eqr
    @25
    @6
    c1
    c1
    cdiv
    @3
    @1
    @6
    @27
    c1
    cN
    cc0
    cA
    cexp
    oveq2
    @28
    sylan9eqr
    oveq2d
    3eqtr4a
    jaodan
    sylan2b
end
