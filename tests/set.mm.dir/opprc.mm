include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "c0.mm"
include "cif.mm"
include "dfopif.mm"
include "iffalse.mm"
include "syl5eq.mm"

theorem opprc
  let cA: class A
  let cB: class B


  assert |- ( -. ( A e. _V /\ B e. _V ) -> <. A , B >. = (/) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    wn
    cA
    cB
    cop
    @0
    cA
    csn
    cA
    cB
    cpr
    cpr
    #
    c0
    cif
    c0
    cA
    cB
    dfopif
    @0
    @1
    c0
    iffalse
    syl5eq
end
