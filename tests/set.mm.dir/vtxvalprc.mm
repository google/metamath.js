include "cvv.mm"
include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "df-nel.mm"
include "fvprc.mm"
include "sylbi.mm"

theorem vtxvalprc
  let cC: class C


  assert |- ( C e/ _V -> ( Vtx ` C ) = (/) )

  proof
    cC
    cvv
    wnel
    cC
    cvv
    wcel
    wn
    cC
    cvtx
    cfv
    c0
    wceq
    cC
    cvv
    df-nel
    cC
    cvtx
    fvprc
    sylbi
end
