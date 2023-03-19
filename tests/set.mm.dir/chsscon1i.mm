include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "choccli.mm"
include "chsscon3i.mm"
include "pjococi.mm"
include "sseq2i.mm"
include "bitri.mm"

theorem chsscon1i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( ( _|_ ` A ) C_ B <-> ( _|_ ` B ) C_ A )

  proof
    cA
    cort
    cfv
    #
    cB
    wss
    cB
    cort
    cfv
    #
    @0
    cort
    cfv
    #
    wss
    @1
    cA
    wss
    @0
    cB
    cA
    ch0le.1
    choccli
    chjcl.2
    chsscon3i
    @2
    cA
    @1
    cA
    ch0le.1
    pjococi
    sseq2i
    bitri
end
