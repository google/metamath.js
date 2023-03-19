include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cplpq.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "cpli.mm"
include "cxp.mm"
include "wceq.mm"
include "opelxpi.mm"
include "addpipq2.mm"
include "syl2an.mm"
include "op1stg.mm"
include "op2ndg.mm"
include "oveqan12d.mm"
include "oveqan12rd.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "eqtrd.mm"

theorem addpipq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. N. /\ B e. N. ) /\ ( C e. N. /\ D e. N. ) ) -> ( <. A , B >. +pQ <. C , D >. ) = <. ( ( A .N D ) +N ( C .N B ) ) , ( B .N D ) >. )

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
    cplpq
    co
    #
    @3
    c1st
    cfv
    #
    @4
    c2nd
    cfv
    #
    cmi
    co
    #
    @4
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    cmi
    co
    #
    cpli
    co
    #
    @10
    @7
    cmi
    co
    #
    cop
    #
    cA
    cD
    cmi
    co
    #
    cC
    cB
    cmi
    co
    #
    cpli
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
    @19
    wcel
    @5
    @14
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
    addpipq2
    syl2an
    @2
    @12
    @17
    @13
    @18
    @2
    @8
    @15
    @11
    @16
    cpli
    @0
    @1
    @6
    cA
    @7
    cD
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
    op2ndg
    #
    oveqan12d
    @1
    @0
    @9
    cC
    @10
    cB
    cmi
    cC
    cD
    cnpi
    cnpi
    op1stg
    cA
    cB
    cnpi
    cnpi
    op2ndg
    #
    oveqan12rd
    oveq12d
    @0
    @1
    @10
    cB
    @7
    cD
    cmi
    @21
    @20
    oveqan12d
    opeq12d
    eqtrd
end
