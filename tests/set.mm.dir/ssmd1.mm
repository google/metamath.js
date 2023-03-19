include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "cmd.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wi.mm"
include "wral.mm"
include "inss1.mm"
include "wceq.mm"
include "dfss.mm"
include "biimpi.mm"
include "oveq2d.mm"
include "syl5sseq.mm"
include "a1d.mm"
include "ralrimivw.mm"
include "mdbr2.mm"
include "syl5ibr.mm"
include "3impia.mm"

theorem ssmd1
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CH /\ B e. CH /\ A C_ B ) -> A MH B )

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
    cmd
    wbr
    #
    @2
    @3
    @0
    @1
    wa
    vx
    cv
    #
    cB
    wss
    #
    @4
    cA
    chj
    co
    #
    cB
    cin
    #
    @4
    cA
    cB
    cin
    #
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    @2
    @11
    vx
    cch
    @2
    @10
    @5
    @2
    @6
    @7
    @9
    @6
    cB
    inss1
    @2
    cA
    @8
    @4
    chj
    @2
    cA
    @8
    wceq
    cA
    cB
    dfss
    biimpi
    oveq2d
    syl5sseq
    a1d
    ralrimivw
    vx
    cA
    cB
    mdbr2
    syl5ibr
    3impia
end
