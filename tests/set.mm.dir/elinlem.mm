include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cfv.mm"
include "elin.mm"
include "fvi.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem elinlem
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B i^i C ) <-> ( A e. B /\ ( _I ` A ) e. C ) )

  proof
    cA
    cB
    cC
    cin
    wcel
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wa
    @0
    cA
    cid
    cfv
    #
    cC
    wcel
    #
    wa
    cA
    cB
    cC
    elin
    @0
    @1
    @3
    @0
    cA
    @2
    cC
    @0
    @2
    cA
    cA
    cB
    fvi
    eqcomd
    eleq1d
    pm5.32i
    bitri
end
