include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cfa.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprod.mm"
include "elnn0.mm"
include "cmul.mm"
include "cid.mm"
include "cseq.mm"
include "facnn.mm"
include "cvv.mm"
include "wa.mm"
include "vex.mm"
include "fvi.mm"
include "mp1i.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "cc.mm"
include "elfznn.mm"
include "nncnd.mm"
include "adantl.mm"
include "fprodser.mm"
include "eqtr4d.mm"
include "c0.mm"
include "prod0.mm"
include "eqcomi.mm"
include "fveq2.mm"
include "fac0.mm"
include "syl6eq.mm"
include "oveq2.mm"
include "fz10.mm"
include "prodeq1d.mm"
include "3eqtr4a.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem fprodfac
  let cA: class A
  let vk: setvar k

  disjoint A k
  assert |- ( A e. NN0 -> ( ! ` A ) = prod_ k e. ( 1 ... A ) k )

  proof
    cA
    cn0
    wcel
    cA
    cn
    wcel
    #
    cA
    cc0
    wceq
    #
    wo
    cA
    cfa
    cfv
    #
    c1
    cA
    cfz
    co
    #
    vk
    cv
    #
    vk
    cprod
    #
    wceq
    #
    cA
    elnn0
    @0
    @6
    @1
    @0
    @2
    cA
    cmul
    cid
    c1
    cseq
    cfv
    @5
    cA
    facnn
    @0
    @4
    vk
    cid
    c1
    cA
    @4
    cvv
    wcel
    @4
    cid
    cfv
    @4
    wceq
    @0
    @4
    @3
    wcel
    #
    wa
    vk
    vex
    @4
    cvv
    fvi
    mp1i
    @0
    cA
    c1
    cuz
    cfv
    wcel
    cA
    elnnuz
    biimpi
    @7
    @4
    cc
    wcel
    @0
    @7
    @4
    @4
    cA
    elfznn
    nncnd
    adantl
    fprodser
    eqtr4d
    @1
    c1
    c0
    @4
    vk
    cprod
    #
    @2
    @5
    @8
    c1
    @4
    vk
    prod0
    eqcomi
    @1
    @2
    cc0
    cfa
    cfv
    c1
    cA
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    @1
    @3
    c0
    @4
    vk
    @1
    @3
    c1
    cc0
    cfz
    co
    c0
    cA
    cc0
    c1
    cfz
    oveq2
    fz10
    syl6eq
    prodeq1d
    3eqtr4a
    jaoi
    sylbi
end
