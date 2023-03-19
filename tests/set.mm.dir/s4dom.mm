include "wcel.mm"
include "wa.mm"
include "cs4.mm"
include "wceq.mm"
include "cdm.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c3.mm"
include "cun.mm"
include "dmeq.mm"
include "cop.mm"
include "s4prop.mm"
include "dmeqd.mm"
include "dmun.mm"
include "dmpropg.mm"
include "adantr.mm"
include "adantl.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "ex.mm"

theorem s4dom
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cE: class E


  assert |- ( ( ( A e. S /\ B e. S ) /\ ( C e. S /\ D e. S ) ) -> ( E = <" A B C D "> -> dom E = ( { 0 , 1 } u. { 2 , 3 } ) ) )

  proof
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    #
    cC
    cS
    wcel
    cD
    cS
    wcel
    wa
    #
    wa
    #
    cE
    cA
    cB
    cC
    cD
    cs4
    #
    wceq
    #
    cE
    cdm
    #
    cc0
    c1
    cpr
    #
    c2
    c3
    cpr
    #
    cun
    #
    wceq
    @4
    @2
    @5
    @3
    cdm
    #
    @8
    cE
    @3
    dmeq
    @2
    @9
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    #
    c2
    cC
    cop
    c3
    cD
    cop
    cpr
    #
    cun
    #
    cdm
    #
    @8
    @2
    @3
    @12
    cA
    cB
    cC
    cD
    cS
    s4prop
    dmeqd
    @2
    @13
    @10
    cdm
    #
    @11
    cdm
    #
    cun
    @8
    @10
    @11
    dmun
    @2
    @14
    @6
    @15
    @7
    @0
    @14
    @6
    wceq
    @1
    cc0
    cA
    c1
    cB
    cS
    cS
    dmpropg
    adantr
    @1
    @15
    @7
    wceq
    @0
    c2
    cC
    c3
    cD
    cS
    cS
    dmpropg
    adantl
    uneq12d
    syl5eq
    eqtrd
    sylan9eqr
    ex
end
