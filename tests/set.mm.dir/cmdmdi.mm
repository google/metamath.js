include "cort.mm"
include "cfv.mm"
include "ccm.mm"
include "wbr.mm"
include "cmd.mm"
include "cdmd.mm"
include "choccli.mm"
include "cmmdi.mm"
include "cmcm4i.mm"
include "cch.mm"
include "wcel.mm"
include "wb.mm"
include "dmdmd.mm"
include "mp2an.mm"
include "3imtr4i.mm"

theorem cmdmdi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH


  assert |- ( A C_H B -> A MH* B )

  proof
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    ccm
    wbr
    @0
    @1
    cmd
    wbr
    #
    cA
    cB
    ccm
    wbr
    cA
    cB
    cdmd
    wbr
    #
    @0
    @1
    cA
    sumdmdi.1
    choccli
    cB
    sumdmdi.2
    choccli
    cmmdi
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    cmcm4i
    cA
    cch
    wcel
    cB
    cch
    wcel
    @3
    @2
    wb
    sumdmdi.1
    sumdmdi.2
    cA
    cB
    dmdmd
    mp2an
    3imtr4i
end
