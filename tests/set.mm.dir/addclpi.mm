include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cpli.mm"
include "co.mm"
include "coa.mm"
include "addpiord.mm"
include "com.mm"
include "pinn.mm"
include "c0.mm"
include "wne.mm"
include "nnacl.mm"
include "sylan2.mm"
include "elni2.mm"
include "wi.mm"
include "nnaordi.mm"
include "ne0i.mm"
include "syl6.mm"
include "expcom.mm"
include "imp32.mm"
include "sylan2b.mm"
include "elni.mm"
include "sylanbrc.mm"
include "sylan.mm"
include "eqeltrd.mm"

theorem addclpi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. N. /\ B e. N. ) -> ( A +N B ) e. N. )

  proof
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    wa
    cA
    cB
    cpli
    co
    cA
    cB
    coa
    co
    #
    cnpi
    cA
    cB
    addpiord
    @0
    cA
    com
    wcel
    #
    @1
    @2
    cnpi
    wcel
    #
    cA
    pinn
    @3
    @1
    wa
    @2
    com
    wcel
    #
    @2
    c0
    wne
    #
    @4
    @1
    @3
    cB
    com
    wcel
    #
    @5
    cB
    pinn
    cA
    cB
    nnacl
    sylan2
    @1
    @3
    @7
    c0
    cB
    wcel
    #
    wa
    @6
    cB
    elni2
    @3
    @7
    @8
    @6
    @7
    @3
    @8
    @6
    wi
    @7
    @3
    wa
    @8
    cA
    c0
    coa
    co
    #
    @2
    wcel
    @6
    c0
    cB
    cA
    nnaordi
    @2
    @9
    ne0i
    syl6
    expcom
    imp32
    sylan2b
    @2
    elni
    sylanbrc
    sylan
    eqeltrd
end
