include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cmd.mm"
include "wbr.mm"
include "wa.mm"
include "chsscon3.mm"
include "wi.mm"
include "choccl.mm"
include "ssmd1.mm"
include "3expia.mm"
include "syl2anr.mm"
include "sylbid.mm"
include "3impia.mm"

theorem ssdmd2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH /\ A C_ B ) -> ( _|_ ` B ) MH ( _|_ ` A ) )

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
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    cmd
    wbr
    #
    @0
    @1
    wa
    @2
    @3
    @4
    wss
    #
    @5
    cA
    cB
    chsscon3
    @1
    @3
    cch
    wcel
    #
    @4
    cch
    wcel
    #
    @6
    @5
    wi
    @0
    cB
    choccl
    cA
    choccl
    @7
    @8
    @6
    @5
    @3
    @4
    ssmd1
    3expia
    syl2anr
    sylbid
    3impia
end
