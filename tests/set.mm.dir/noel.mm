include "c0.mm"
include "wcel.mm"
include "cvv.mm"
include "cdif.mm"
include "eldifi.mm"
include "eldifn.mm"
include "pm2.65i.mm"
include "df-nul.mm"
include "eleq2i.mm"
include "mtbir.mm"

theorem noel
  param cA: class A


  assert |- -. A e. (/)

  proof
    cA
    c0
    wcel
    cA
    cvv
    cvv
    cdif
    #
    wcel
    #
    @1
    cA
    cvv
    wcel
    cA
    cvv
    cvv
    eldifi
    cA
    cvv
    cvv
    eldifn
    pm2.65i
    c0
    @0
    cA
    df-nul
    eleq2i
    mtbir
end
