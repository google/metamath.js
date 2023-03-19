include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "wfr.mm"
include "wwe.mm"
include "wpo.mm"
include "sopo.mm"
include "frfi.mm"
include "sylan.mm"
include "simpl.mm"
include "df-we.mm"
include "sylanbrc.mm"

theorem wofi
  let cA: class A
  let cR: class R


  assert |- ( ( R Or A /\ A e. Fin ) -> R We A )

  proof
    cA
    cR
    wor
    #
    cA
    cfn
    wcel
    #
    wa
    cA
    cR
    wfr
    #
    @0
    cA
    cR
    wwe
    @0
    cA
    cR
    wpo
    @1
    @2
    cA
    cR
    sopo
    cA
    cR
    frfi
    sylan
    @0
    @1
    simpl
    cA
    cR
    df-we
    sylanbrc
end
