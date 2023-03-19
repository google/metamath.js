include "cec.mm"
include "csn.mm"
include "cima.mm"
include "cqs.mm"
include "cuni.mm"
include "df-ec.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "uniqs.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem ecqs
  let cA: class A
  let cR: class R
  assume ecqs.1: |- R e. _V


  assert |- [ A ] R = U. ( { A } /. R )

  proof
    cA
    cR
    cec
    cR
    cA
    csn
    #
    cima
    #
    @0
    cR
    cqs
    cuni
    #
    cA
    cR
    df-ec
    cR
    cvv
    wcel
    @2
    @1
    wceq
    ecqs.1
    @0
    cR
    cvv
    uniqs
    ax-mp
    eqtr4i
end
