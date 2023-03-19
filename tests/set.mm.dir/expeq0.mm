include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "bibi1d.mm"
include "imbi2d.mm"
include "exp1.mm"
include "wa.mm"
include "wo.mm"
include "cn0.mm"
include "nnnn0.mm"
include "cmul.mm"
include "expp1.mm"
include "expcl.mm"
include "simpl.mm"
include "mul0ord.mm"
include "bitrd.mm"
include "sylan2.mm"
include "biimp.mm"
include "idd.mm"
include "jaod.mm"
include "olc.mm"
include "impbid1.mm"
include "sylan9bb.mm"
include "exp31.mm"
include "com12.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem expeq0
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( A e. CC /\ N e. NN ) -> ( ( A ^ N ) = 0 <-> A = 0 ) )

  proof
    cN
    cn
    wcel
    cA
    cc
    wcel
    #
    cA
    cN
    cexp
    co
    #
    cc0
    wceq
    #
    cA
    cc0
    wceq
    #
    wb
    #
    @0
    cA
    vj
    cv
    #
    cexp
    co
    #
    cc0
    wceq
    #
    @3
    wb
    #
    wi
    @0
    cA
    c1
    cexp
    co
    #
    cc0
    wceq
    #
    @3
    wb
    #
    wi
    @0
    cA
    vk
    cv
    #
    cexp
    co
    #
    cc0
    wceq
    #
    @3
    wb
    #
    wi
    @0
    cA
    @12
    c1
    caddc
    co
    #
    cexp
    co
    #
    cc0
    wceq
    #
    @3
    wb
    #
    wi
    @0
    @4
    wi
    vj
    vk
    cN
    @5
    c1
    wceq
    #
    @8
    @11
    @0
    @20
    @7
    @10
    @3
    @20
    @6
    @9
    cc0
    @5
    c1
    cA
    cexp
    oveq2
    eqeq1d
    bibi1d
    imbi2d
    @5
    @12
    wceq
    #
    @8
    @15
    @0
    @21
    @7
    @14
    @3
    @21
    @6
    @13
    cc0
    @5
    @12
    cA
    cexp
    oveq2
    eqeq1d
    bibi1d
    imbi2d
    @5
    @16
    wceq
    #
    @8
    @19
    @0
    @22
    @7
    @18
    @3
    @22
    @6
    @17
    cc0
    @5
    @16
    cA
    cexp
    oveq2
    eqeq1d
    bibi1d
    imbi2d
    @5
    cN
    wceq
    #
    @8
    @4
    @0
    @23
    @7
    @2
    @3
    @23
    @6
    @1
    cc0
    @5
    cN
    cA
    cexp
    oveq2
    eqeq1d
    bibi1d
    imbi2d
    @0
    @9
    cA
    cc0
    cA
    exp1
    eqeq1d
    @12
    cn
    wcel
    #
    @0
    @15
    @19
    @0
    @24
    @15
    @19
    wi
    @0
    @24
    @15
    @19
    @0
    @24
    wa
    @18
    @14
    @3
    wo
    #
    @15
    @3
    @24
    @0
    @12
    cn0
    wcel
    #
    @18
    @25
    wb
    @12
    nnnn0
    @0
    @26
    wa
    #
    @18
    @13
    cA
    cmul
    co
    #
    cc0
    wceq
    @25
    @27
    @17
    @28
    cc0
    cA
    @12
    expp1
    eqeq1d
    @27
    @13
    cA
    cA
    @12
    expcl
    @0
    @26
    simpl
    mul0ord
    bitrd
    sylan2
    @15
    @25
    @3
    @15
    @14
    @3
    @3
    @14
    @3
    biimp
    @15
    @3
    idd
    jaod
    @3
    @14
    olc
    impbid1
    sylan9bb
    exp31
    com12
    a2d
    nnind
    impcom
end
