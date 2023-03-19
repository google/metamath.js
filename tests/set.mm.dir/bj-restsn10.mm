include "wcel.mm"
include "c0.mm"
include "wss.mm"
include "csn.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "0ss.mm"
include "bj-restsnss.mm"
include "mpan2.mm"

theorem bj-restsn10
  let cV: class V
  let cX: class X


  assert |- ( X e. V -> ( { X } |`t (/) ) = { (/) } )

  proof
    cX
    cV
    wcel
    c0
    cX
    wss
    cX
    csn
    c0
    crest
    co
    c0
    csn
    wceq
    cX
    0ss
    c0
    cV
    cX
    bj-restsnss
    mpan2
end
