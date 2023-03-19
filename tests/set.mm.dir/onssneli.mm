include "wss.mm"
include "wcel.mm"
include "ssel.mm"
include "con0.mm"
include "word.mm"
include "wn.mm"
include "oneli.mm"
include "eloni.mm"
include "ordirr.mm"
include "3syl.mm"
include "nsyli.mm"
include "pm2.01d.mm"

theorem onssneli
  let cA: class A
  let cB: class B
  assume on.1: |- A e. On


  assert |- ( A C_ B -> -. B e. A )

  proof
    cA
    cB
    wss
    #
    cB
    cA
    wcel
    #
    @0
    @1
    cB
    cB
    wcel
    #
    @1
    cA
    cB
    cB
    ssel
    @1
    cB
    con0
    wcel
    cB
    word
    @2
    wn
    cA
    cB
    on.1
    oneli
    cB
    eloni
    cB
    ordirr
    3syl
    nsyli
    pm2.01d
end
