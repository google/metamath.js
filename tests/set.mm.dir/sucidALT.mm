include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "wcel.mm"
include "snid.mm"
include "elun1.mm"
include "ax-mp.mm"
include "df-suc.mm"
include "equncomi.mm"
include "eleqtrri.mm"

theorem sucidALT
  let cA: class A
  assume sucidALT.1: |- A e. _V


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
    sucidALT.1
    snid
    cA
    @0
    cA
    elun1
    ax-mp
    @2
    cA
    @0
    cA
    df-suc
    equncomi
    eleqtrri
end
