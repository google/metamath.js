include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cmpq.mm"
include "co.mm"
include "wceq.mm"
include "c1st.mm"
include "cfv.mm"
include "cmi.mm"
include "c2nd.mm"
include "cop.mm"
include "mulcompi.mm"
include "opeq12i.mm"
include "mulpipq2.mm"
include "ancoms.mm"
include "3eqtr4a.mm"
include "mulpqf.mm"
include "fdmi.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem mulcompq
  let cA: class A
  let cB: class B


  assert |- ( A .pQ B ) = ( B .pQ A )

  proof
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    cmpq
    co
    #
    cB
    cA
    cmpq
    co
    #
    wceq
    @3
    cA
    c1st
    cfv
    #
    cB
    c1st
    cfv
    #
    cmi
    co
    #
    cA
    c2nd
    cfv
    #
    cB
    c2nd
    cfv
    #
    cmi
    co
    #
    cop
    @7
    @6
    cmi
    co
    #
    @10
    @9
    cmi
    co
    #
    cop
    #
    @4
    @5
    @8
    @12
    @11
    @13
    @6
    @7
    mulcompi
    @9
    @10
    mulcompi
    opeq12i
    cA
    cB
    mulpipq2
    @2
    @1
    @5
    @14
    wceq
    cB
    cA
    mulpipq2
    ancoms
    3eqtr4a
    cA
    cB
    @0
    cmpq
    @0
    @0
    cxp
    @0
    cmpq
    mulpqf
    fdmi
    ndmovcom
    pm2.61i
end
