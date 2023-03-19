include "ccnv.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cid.mm"
include "cfv.mm"
include "wa.mm"
include "cnvcnv.mm"
include "incom.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "elinlem.mm"
include "bitri.mm"

theorem elcnvcnvlem
  let cA: class A
  let cB: class B


  assert |- ( A e. `' `' B <-> ( A e. ( _V X. _V ) /\ ( _I ` A ) e. B ) )

  proof
    cA
    cB
    ccnv
    ccnv
    #
    wcel
    cA
    cvv
    cvv
    cxp
    #
    cB
    cin
    #
    wcel
    cA
    @1
    wcel
    cA
    cid
    cfv
    cB
    wcel
    wa
    @0
    @2
    cA
    @0
    cB
    @1
    cin
    @2
    cB
    cnvcnv
    cB
    @1
    incom
    eqtri
    eleq2i
    cA
    @1
    cB
    elinlem
    bitri
end
