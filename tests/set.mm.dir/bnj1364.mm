include "w-bnj15.mm"
include "wfr.mm"
include "w-bnj13.mm"
include "df-bnj15.mm"
include "simprbi.mm"

theorem bnj1364
  let cA: class A
  let cR: class R


  assert |- ( R _FrSe A -> R _Se A )

  proof
    cA
    cR
    w-bnj15
    cA
    cR
    wfr
    cA
    cR
    w-bnj13
    cA
    cR
    df-bnj15
    simprbi
end
