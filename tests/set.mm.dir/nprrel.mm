include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "brrelexi.mm"
include "mto.mm"

theorem nprrel
  let cA: class A
  let cB: class B
  let cR: class R
  assume nprrel12.1: |- Rel R
  assume nprrel.2: |- -. A e. _V


  assert |- -. A R B

  proof
    cA
    cB
    cR
    wbr
    cA
    cvv
    wcel
    nprrel.2
    cA
    cB
    cR
    nprrel12.1
    brrelexi
    mto
end
