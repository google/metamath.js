include "csh.mm"
include "wcel.mm"
include "cc.mm"
include "csm.mm"
include "co.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cva.mm"
include "chil.mm"
include "wss.mm"
include "c0v.mm"
include "issh2.mm"
include "simprbi.mm"
include "simprd.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem shmulcl
  let cA: class A
  let cB: class B
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( H e. SH /\ A e. CC /\ B e. H ) -> ( A .h B ) e. H )

  proof
    cH
    csh
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cH
    wcel
    #
    cA
    cB
    csm
    co
    #
    cH
    wcel
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    #
    cH
    wcel
    #
    vy
    cH
    wral
    vx
    cc
    wral
    #
    @1
    @2
    wa
    @4
    @0
    @5
    @6
    cva
    co
    cH
    wcel
    vy
    cH
    wral
    vx
    cH
    wral
    #
    @9
    @0
    cH
    chil
    wss
    c0v
    cH
    wcel
    wa
    @10
    @9
    wa
    vx
    vy
    cH
    issh2
    simprbi
    simprd
    @8
    @4
    cA
    @6
    csm
    co
    #
    cH
    wcel
    vx
    vy
    cA
    cB
    cc
    cH
    @5
    cA
    wceq
    @7
    @11
    cH
    @5
    cA
    @6
    csm
    oveq1
    eleq1d
    @6
    cB
    wceq
    @11
    @3
    cH
    @6
    cB
    cA
    csm
    oveq2
    eleq1d
    rspc2v
    syl5com
    3impib
end
