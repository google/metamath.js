include "c0.mm"
include "whe.mm"
include "cima.mm"
include "wss.mm"
include "ima0.mm"
include "eqimssi.mm"
include "df-he.mm"
include "mpbir.mm"

theorem he0
  let cA: class A


  assert |- A hereditary (/)

  proof
    c0
    cA
    whe
    cA
    c0
    cima
    #
    c0
    wss
    @0
    c0
    cA
    ima0
    eqimssi
    c0
    cA
    df-he
    mpbir
end
