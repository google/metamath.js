include "wpss.mm"
include "wss.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "dfpss2.mm"
include "eqss.mm"
include "baib.mm"
include "notbid.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem dfpss3
  let cA: class A
  let cB: class B


  assert |- ( A C. B <-> ( A C_ B /\ -. B C_ A ) )

  proof
    cA
    cB
    wpss
    cA
    cB
    wss
    #
    cA
    cB
    wceq
    #
    wn
    #
    wa
    @0
    cB
    cA
    wss
    #
    wn
    #
    wa
    cA
    cB
    dfpss2
    @0
    @2
    @4
    @0
    @1
    @3
    @1
    @0
    @3
    cA
    cB
    eqss
    baib
    notbid
    pm5.32i
    bitri
end
