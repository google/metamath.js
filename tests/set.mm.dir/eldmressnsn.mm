include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "snidg.mm"
include "dmressnsn.mm"
include "eleqtrrd.mm"

theorem eldmressnsn
  let cA: class A
  let cF: class F


  assert |- ( A e. dom F -> A e. dom ( F |` { A } ) )

  proof
    cA
    cF
    cdm
    #
    wcel
    cA
    cA
    csn
    #
    cF
    @1
    cres
    cdm
    cA
    @0
    snidg
    cA
    cF
    dmressnsn
    eleqtrrd
end
