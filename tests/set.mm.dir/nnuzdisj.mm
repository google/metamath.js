include "c1.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "cin.mm"
include "cc0.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "fz1ssfz0.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "nn0disj.mm"
include "sseq0.mm"
include "mp2an.mm"

theorem nnuzdisj
  let cN: class N


  assert |- ( ( 1 ... N ) i^i ( ZZ>= ` ( N + 1 ) ) ) = (/)

  proof
    c1
    cN
    cfz
    co
    #
    cN
    c1
    caddc
    co
    cuz
    cfv
    #
    cin
    #
    cc0
    cN
    cfz
    co
    #
    @1
    cin
    #
    wss
    #
    @4
    c0
    wceq
    @2
    c0
    wceq
    @0
    @3
    wss
    @5
    cN
    fz1ssfz0
    @0
    @3
    @1
    ssrin
    ax-mp
    cN
    nn0disj
    @2
    @4
    sseq0
    mp2an
end
