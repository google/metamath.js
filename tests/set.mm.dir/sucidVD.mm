include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "wcel.mm"
include "snid.mm"
include "elun2.mm"
include "e0a.mm"
include "df-suc.mm"
include "eleqtrri.mm"

theorem sucidVD
  let cA: class A
  assume sucidVD.1: |- A e. _V


  assert |- A e. suc A

  proof
    cA
    cA
    cA
    csn
    #
    cun
    #
    cA
    csuc
    cA
    @0
    wcel
    cA
    @1
    wcel
    cA
    sucidVD.1
    snid
    cA
    @0
    cA
    elun2
    e0a
    cA
    df-suc
    eleqtrri
end
