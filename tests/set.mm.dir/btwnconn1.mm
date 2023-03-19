include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "wceq.mm"
include "breq1.mm"
include "3anbi3d.mm"
include "orc.mm"
include "3ad2ant3.mm"
include "syl6bi.mm"
include "adantld.mm"
include "simpr1.mm"
include "simpl.mm"
include "3simpc.mm"
include "adantl.mm"
include "jca31.mm"
include "btwnconn1lem14.mm"
include "sylan2.mm"
include "an12s.mm"
include "ex.mm"
include "pm2.61ine.mm"

theorem btwnconn1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( A =/= B /\ B Btwn <. A , C >. /\ B Btwn <. A , D >. ) -> ( C Btwn <. A , D >. \/ D Btwn <. A , C >. ) ) )

  proof
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @0
    wcel
    wa
    cC
    @0
    wcel
    cD
    @0
    wcel
    wa
    w3a
    #
    cA
    cB
    wne
    #
    cB
    cA
    cC
    cop
    #
    cbtwn
    wbr
    #
    cB
    cA
    cD
    cop
    #
    cbtwn
    wbr
    #
    w3a
    #
    cC
    @5
    cbtwn
    wbr
    #
    cD
    @3
    cbtwn
    wbr
    #
    wo
    #
    @1
    @7
    wa
    #
    @10
    wi
    cB
    cC
    cB
    cC
    wceq
    #
    @7
    @10
    @1
    @12
    @7
    @2
    @4
    @8
    w3a
    @10
    @12
    @6
    @8
    @2
    @4
    cB
    cC
    @5
    cbtwn
    breq1
    3anbi3d
    @8
    @2
    @10
    @4
    @8
    @9
    orc
    3ad2ant3
    syl6bi
    adantld
    cB
    cC
    wne
    #
    @11
    @10
    @1
    @13
    @7
    @10
    @13
    @7
    wa
    #
    @1
    @2
    @13
    wa
    @4
    @6
    wa
    #
    wa
    @10
    @14
    @2
    @13
    @15
    @13
    @2
    @4
    @6
    simpr1
    @13
    @7
    simpl
    @7
    @15
    @13
    @2
    @4
    @6
    3simpc
    adantl
    jca31
    cA
    cB
    cC
    cD
    cN
    btwnconn1lem14
    sylan2
    an12s
    ex
    pm2.61ine
    ex
end
