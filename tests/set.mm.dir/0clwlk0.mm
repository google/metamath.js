include "c0.mm"
include "cclwlks.mm"
include "cfv.mm"
include "cwlks.mm"
include "wss.mm"
include "wceq.mm"
include "clwlkswks.mm"
include "0wlk0.mm"
include "sseq0.mm"
include "mp2an.mm"

theorem 0clwlk0



  assert |- ( ClWalks ` (/) ) = (/)

  proof
    c0
    cclwlks
    cfv
    #
    c0
    cwlks
    cfv
    #
    wss
    @1
    c0
    wceq
    @0
    c0
    wceq
    c0
    clwlkswks
    0wlk0
    @0
    @1
    sseq0
    mp2an
end
