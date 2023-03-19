include "cnq.mm"
include "wcel.mm"
include "wa.mm"
include "cmq.mm"
include "co.mm"
include "wceq.mm"
include "cmpq.mm"
include "cerq.mm"
include "cfv.mm"
include "mulcompq.mm"
include "fveq2i.mm"
include "mulpqnq.mm"
include "ancoms.mm"
include "3eqtr4a.mm"
include "cxp.mm"
include "mulnqf.mm"
include "fdmi.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem mulcomnq
  let cA: class A
  let cB: class B


  assert |- ( A .Q B ) = ( B .Q A )

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
    cmq
    co
    #
    cB
    cA
    cmq
    co
    #
    wceq
    @2
    cA
    cB
    cmpq
    co
    #
    cerq
    cfv
    cB
    cA
    cmpq
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
    mulcompq
    fveq2i
    cA
    cB
    mulpqnq
    @1
    @0
    @4
    @7
    wceq
    cB
    cA
    mulpqnq
    ancoms
    3eqtr4a
    cA
    cB
    cnq
    cmq
    cnq
    cnq
    cxp
    cnq
    cmq
    mulnqf
    fdmi
    ndmovcom
    pm2.61i
end
