include "cn0.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "c2o.mm"
include "wcad.mm"
include "c1o.mm"
include "cif.mm"
include "cmpt2.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "whad.mm"
include "crab.mm"
include "csad.mm"
include "wb.mm"
include "hadcoma.mm"
include "a1i.mm"
include "rabbidv.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "sadfval.mm"
include "cadcoma.mm"
include "ifbid.mm"
include "mpt2eq3ia.mm"
include "seqeq2.mm"
include "ax-mp.mm"
include "3eqtr4d.mm"

theorem sadcom
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n


  assert |- ( ( A C_ NN0 /\ B C_ NN0 ) -> ( A sadd B ) = ( B sadd A ) )

  proof
    cA
    cn0
    wss
    #
    cB
    cn0
    wss
    #
    wa
    #
    vk
    cv
    #
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    c0
    @3
    vc
    vm
    c2o
    cn0
    vm
    cv
    #
    cA
    wcel
    #
    @6
    cB
    wcel
    #
    c0
    vc
    cv
    #
    wcel
    #
    wcad
    #
    c1o
    c0
    cif
    #
    cmpt2
    #
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    c0
    @14
    c1
    cmin
    co
    cif
    cmpt
    #
    cc0
    cseq
    #
    cfv
    wcel
    #
    whad
    #
    vk
    cn0
    crab
    @5
    @4
    @17
    whad
    #
    vk
    cn0
    crab
    cA
    cB
    csad
    co
    cB
    cA
    csad
    co
    @2
    @18
    @19
    vk
    cn0
    @18
    @19
    wb
    @2
    @4
    @5
    @17
    hadcoma
    a1i
    rabbidv
    @2
    cA
    cB
    @16
    vk
    vm
    vn
    vc
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @16
    eqid
    sadfval
    @2
    cB
    cA
    @16
    vk
    vm
    vn
    vc
    @21
    @20
    @13
    vc
    vm
    c2o
    cn0
    @8
    @7
    @10
    wcad
    #
    c1o
    c0
    cif
    #
    cmpt2
    #
    wceq
    @16
    @24
    @15
    cc0
    cseq
    wceq
    vc
    vm
    c2o
    cn0
    @12
    @23
    @9
    c2o
    wcel
    @6
    cn0
    wcel
    wa
    #
    @11
    @22
    c1o
    c0
    @11
    @22
    wb
    @25
    @7
    @8
    @10
    cadcoma
    a1i
    ifbid
    mpt2eq3ia
    @13
    @24
    @15
    cc0
    seqeq2
    ax-mp
    sadfval
    3eqtr4d
end
