include "wcel.mm"
include "c0.mm"
include "wss.mm"
include "wa.mm"
include "csn.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "0ss.mm"
include "jctr.mm"
include "bj-restsnss2.mm"
include "syl.mm"

theorem bj-restsn0
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( { (/) } |`t A ) = { (/) } )

  proof
    cA
    cV
    wcel
    #
    @0
    c0
    cA
    wss
    #
    wa
    c0
    csn
    #
    cA
    crest
    co
    @2
    wceq
    @0
    @1
    cA
    0ss
    jctr
    cA
    cV
    c0
    bj-restsnss2
    syl
end
