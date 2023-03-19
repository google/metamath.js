include "wa.mm"
include "w3a.mm"
include "df-3an.mm"
include "mtbi.mm"
include "imnani.mm"

theorem bnj1224
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume bnj1224.1: |- -. ( th /\ ta /\ et )


  assert |- ( ( th /\ ta ) -> -. et )

  proof
    wth
    wta
    wa
    #
    wet
    wth
    wta
    wet
    w3a
    @0
    wet
    wa
    bnj1224.1
    wth
    wta
    wet
    df-3an
    mtbi
    imnani
end
