include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "wcel.mm"
include "snid.mm"
include "elun1.mm"
include "e0a.mm"
include "df-suc.mm"
include "equncomi.mm"
include "eleqtrri.mm"

theorem sucidALTVD
  let cA: class A
  assume sucidALTVD.1: |- A e. _V


  assert |- A e. suc A

  proof
    cA
    cA
    csn
    #
    cA
    cun
    #
    cA
    csuc
    #
    cA
    @0
    wcel
    cA
    @1
    wcel
    cA
    sucidALTVD.1
    snid
    cA
    @0
    cA
    elun1
    e0a
    @2
    cA
    @0
    cA
    df-suc
    equncomi
    eleqtrri
end
