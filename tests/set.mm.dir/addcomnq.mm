include "cnq.mm"
include "wcel.mm"
include "wa.mm"
include "cplq.mm"
include "co.mm"
include "wceq.mm"
include "cplpq.mm"
include "cerq.mm"
include "cfv.mm"
include "addcompq.mm"
include "fveq2i.mm"
include "addpqnq.mm"
include "ancoms.mm"
include "3eqtr4a.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem addcomnq
  let cA: class A
  let cB: class B


  assert |- ( A +Q B ) = ( B +Q A )

  proof
    cA
    cnq
    wcel
    #
    cB
    cnq
    wcel
    #
    wa
    #
    cA
    cB
    cplq
    co
    #
    cB
    cA
    cplq
    co
    #
    wceq
    @2
    cA
    cB
    cplpq
    co
    #
    cerq
    cfv
    cB
    cA
    cplpq
    co
    #
    cerq
    cfv
    #
    @3
    @4
    @5
    @6
    cerq
    cA
    cB
    addcompq
    fveq2i
    cA
    cB
    addpqnq
    @1
    @0
    @4
    @7
    wceq
    cB
    cA
    addpqnq
    ancoms
    3eqtr4a
    cA
    cB
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    ndmovcom
    pm2.61i
end
