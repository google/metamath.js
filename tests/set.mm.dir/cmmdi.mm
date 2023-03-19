include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "cdmd.mm"
include "cmd.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "cmcm4i.mm"
include "choccli.mm"
include "osumcor2i.mm"
include "sylbi.mm"
include "sumdmdii.mm"
include "syl.mm"
include "cch.mm"
include "wcel.mm"
include "wb.mm"
include "mddmd.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem cmmdi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH


  assert |- ( A C_H B -> A MH B )

  proof
    cA
    cB
    ccm
    wbr
    #
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cdmd
    wbr
    #
    cA
    cB
    cmd
    wbr
    #
    @0
    @1
    @2
    cph
    co
    @1
    @2
    chj
    co
    wceq
    #
    @3
    @0
    @1
    @2
    ccm
    wbr
    @5
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    cmcm4i
    @1
    @2
    cA
    sumdmdi.1
    choccli
    #
    cB
    sumdmdi.2
    choccli
    #
    osumcor2i
    sylbi
    @1
    @2
    @6
    @7
    sumdmdii
    syl
    cA
    cch
    wcel
    cB
    cch
    wcel
    @4
    @3
    wb
    sumdmdi.1
    sumdmdi.2
    cA
    cB
    mddmd
    mp2an
    sylibr
end
