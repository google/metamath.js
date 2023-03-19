include "wcel.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "ssid.mm"
include "bj-restb.mm"
include "mpani.mm"

theorem bj-resta
  let cA: class A
  let cV: class V
  let cX: class X


  assert |- ( X e. V -> ( A e. X -> A e. ( X |`t A ) ) )

  proof
    cX
    cV
    wcel
    cA
    cA
    wss
    cA
    cX
    wcel
    cA
    cX
    cA
    crest
    co
    wcel
    cA
    ssid
    cA
    cA
    cV
    cX
    bj-restb
    mpani
end
