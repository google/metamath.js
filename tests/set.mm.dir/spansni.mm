include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cort.mm"
include "chil.mm"
include "wcel.mm"
include "wss.mm"
include "snssi.mm"
include "spanssoc.mm"
include "mp2b.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "wi.mm"
include "csh.mm"
include "wral.mm"
include "wa.mm"
include "elexi.mm"
include "snss.mm"
include "shmulcl.mm"
include "3expia.mm"
include "ancoms.mm"
include "syl5bir.mm"
include "eleq1.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "ralrimdva.mm"
include "rexlimiv.mm"
include "h1de2ci.mm"
include "wb.mm"
include "vex.mm"
include "elspani.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem spansni
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  assume spansn.1: |- A e. ~H


  assert |- ( span ` { A } ) = ( _|_ ` ( _|_ ` { A } ) )

  proof
    cA
    csn
    #
    cspn
    cfv
    #
    @0
    cort
    cfv
    cort
    cfv
    #
    cA
    chil
    wcel
    #
    @0
    chil
    wss
    #
    @1
    @2
    wss
    spansn.1
    cA
    chil
    snssi
    #
    @0
    spanssoc
    mp2b
    vx
    @2
    @1
    vx
    cv
    #
    vz
    cv
    #
    cA
    csm
    co
    #
    wceq
    #
    vz
    cc
    wrex
    @0
    vy
    cv
    #
    wss
    #
    @6
    @10
    wcel
    #
    wi
    #
    vy
    csh
    wral
    #
    @6
    @2
    wcel
    @6
    @1
    wcel
    #
    @9
    @14
    vz
    cc
    @7
    cc
    wcel
    #
    @9
    @13
    vy
    csh
    @16
    @10
    csh
    wcel
    #
    wa
    #
    @13
    @9
    @11
    @8
    @10
    wcel
    #
    wi
    @11
    cA
    @10
    wcel
    #
    @18
    @19
    cA
    @10
    cA
    chil
    spansn.1
    elexi
    snss
    @17
    @16
    @20
    @19
    wi
    @17
    @16
    @20
    @19
    @7
    cA
    @10
    shmulcl
    3expia
    ancoms
    syl5bir
    @9
    @12
    @19
    @11
    @6
    @8
    @10
    eleq1
    imbi2d
    syl5ibrcom
    ralrimdva
    rexlimiv
    vz
    @6
    cA
    spansn.1
    h1de2ci
    @3
    @4
    @15
    @14
    wb
    spansn.1
    @5
    vy
    @0
    @6
    vx
    vex
    elspani
    mp2b
    3imtr4i
    ssriv
    eqssi
end
