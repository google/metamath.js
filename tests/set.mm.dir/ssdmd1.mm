include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "cdmd.mm"
include "wbr.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cmd.mm"
include "wi.mm"
include "choccl.mm"
include "ssmd2.mm"
include "3expia.mm"
include "syl2anr.mm"
include "chsscon3.mm"
include "dmdmd.mm"
include "3imtr4d.mm"
include "3impia.mm"

theorem ssdmd1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH /\ A C_ B ) -> A MH* B )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cB
    cdmd
    wbr
    #
    @0
    @1
    wa
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    wss
    #
    @5
    @4
    cmd
    wbr
    #
    @2
    @3
    @1
    @4
    cch
    wcel
    #
    @5
    cch
    wcel
    #
    @6
    @7
    wi
    @0
    cB
    choccl
    cA
    choccl
    @8
    @9
    @6
    @7
    @4
    @5
    ssmd2
    3expia
    syl2anr
    cA
    cB
    chsscon3
    cA
    cB
    dmdmd
    3imtr4d
    3impia
end
