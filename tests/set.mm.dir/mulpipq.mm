include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cmpq.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "cmi.mm"
include "c2nd.mm"
include "cxp.mm"
include "wceq.mm"
include "opelxpi.mm"
include "mulpipq2.mm"
include "syl2an.mm"
include "op1stg.mm"
include "oveqan12d.mm"
include "op2ndg.mm"
include "opeq12d.mm"
include "eqtrd.mm"

theorem mulpipq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. N. /\ B e. N. ) /\ ( C e. N. /\ D e. N. ) ) -> ( <. A , B >. .pQ <. C , D >. ) = <. ( A .N C ) , ( B .N D ) >. )

  proof
    cA
    cnpi
    wcel
    cB
    cnpi
    wcel
    wa
    #
    cC
    cnpi
    wcel
    cD
    cnpi
    wcel
    wa
    #
    wa
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cmpq
    co
    #
    @3
    c1st
    cfv
    #
    @4
    c1st
    cfv
    #
    cmi
    co
    #
    @3
    c2nd
    cfv
    #
    @4
    c2nd
    cfv
    #
    cmi
    co
    #
    cop
    #
    cA
    cC
    cmi
    co
    #
    cB
    cD
    cmi
    co
    #
    cop
    @0
    @3
    cnpi
    cnpi
    cxp
    #
    wcel
    @4
    @15
    wcel
    @5
    @12
    wceq
    @1
    cA
    cB
    cnpi
    cnpi
    opelxpi
    cC
    cD
    cnpi
    cnpi
    opelxpi
    @3
    @4
    mulpipq2
    syl2an
    @2
    @8
    @13
    @11
    @14
    @0
    @1
    @6
    cA
    @7
    cC
    cmi
    cA
    cB
    cnpi
    cnpi
    op1stg
    cC
    cD
    cnpi
    cnpi
    op1stg
    oveqan12d
    @0
    @1
    @9
    cB
    @10
    cD
    cmi
    cA
    cB
    cnpi
    cnpi
    op2ndg
    cC
    cD
    cnpi
    cnpi
    op2ndg
    oveqan12d
    opeq12d
    eqtrd
end
