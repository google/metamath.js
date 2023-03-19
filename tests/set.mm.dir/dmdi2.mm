include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "cdmd.mm"
include "wbr.mm"
include "wss.mm"
include "wa.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "dmdi.mm"
include "eqimss2.mm"
include "syl.mm"

theorem dmdi2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ ( A MH* B /\ B C_ C ) ) -> ( C i^i ( A vH B ) ) C_ ( ( C i^i A ) vH B ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    cC
    cch
    wcel
    w3a
    cA
    cB
    cdmd
    wbr
    cB
    cC
    wss
    wa
    wa
    cC
    cA
    cin
    cB
    chj
    co
    #
    cC
    cA
    cB
    chj
    co
    cin
    #
    wceq
    @1
    @0
    wss
    cA
    cB
    cC
    dmdi
    @1
    @0
    eqimss2
    syl
end
