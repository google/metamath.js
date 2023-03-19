include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cplpq.mm"
include "co.mm"
include "wceq.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "cpli.mm"
include "cop.mm"
include "addcompi.mm"
include "mulcompi.mm"
include "opeq12i.mm"
include "addpipq2.mm"
include "ancoms.mm"
include "3eqtr4a.mm"
include "addpqf.mm"
include "fdmi.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem addcompq
  let cA: class A
  let cB: class B


  assert |- ( A +pQ B ) = ( B +pQ A )

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
    cplpq
    co
    #
    cB
    cA
    cplpq
    co
    #
    wceq
    @3
    cA
    c1st
    cfv
    cB
    c2nd
    cfv
    #
    cmi
    co
    #
    cB
    c1st
    cfv
    cA
    c2nd
    cfv
    #
    cmi
    co
    #
    cpli
    co
    #
    @8
    @6
    cmi
    co
    #
    cop
    @9
    @7
    cpli
    co
    #
    @6
    @8
    cmi
    co
    #
    cop
    #
    @4
    @5
    @10
    @12
    @11
    @13
    @7
    @9
    addcompi
    @8
    @6
    mulcompi
    opeq12i
    cA
    cB
    addpipq2
    @2
    @1
    @5
    @14
    wceq
    cB
    cA
    addpipq2
    ancoms
    3eqtr4a
    cA
    cB
    @0
    cplpq
    @0
    @0
    cxp
    @0
    cplpq
    addpqf
    fdmi
    ndmovcom
    pm2.61i
end
