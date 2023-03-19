include "cn0.mm"
include "wss.mm"
include "wa.mm"
include "csad.mm"
include "co.mm"
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
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "whad.mm"
include "crab.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "sadfval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"

theorem sadcl
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n


  assert |- ( ( A C_ NN0 /\ B C_ NN0 ) -> ( A sadd B ) C_ NN0 )

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
    cA
    cB
    csad
    co
    vk
    cv
    #
    cA
    wcel
    @3
    cB
    wcel
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
    @4
    cB
    wcel
    c0
    vc
    cv
    wcel
    wcad
    c1o
    c0
    cif
    cmpt2
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    c0
    @5
    c1
    cmin
    co
    cif
    cmpt
    cc0
    cseq
    #
    cfv
    wcel
    whad
    #
    vk
    cn0
    crab
    cn0
    @2
    cA
    cB
    @6
    vk
    vm
    vn
    vc
    @0
    @1
    simpl
    @0
    @1
    simpr
    @6
    eqid
    sadfval
    @7
    vk
    cn0
    ssrab2
    syl6eqss
end
