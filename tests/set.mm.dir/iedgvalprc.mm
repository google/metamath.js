include "cvv.mm"
include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "ciedg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "df-nel.mm"
include "fvprc.mm"
include "sylbi.mm"

theorem iedgvalprc
  let cC: class C


  assert |- ( C e/ _V -> ( iEdg ` C ) = (/) )

  proof
    cC
    cvv
    wnel
    cC
    cvv
    wcel
    wn
    cC
    ciedg
    cfv
    c0
    wceq
    cC
    cvv
    df-nel
    cC
    ciedg
    fvprc
    sylbi
end
