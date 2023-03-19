include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjdiv.mm"
include "mp3an12.mm"

theorem cjdivi
  let cA: class A
  let cB: class B
  assume recl.1: |- A e. CC
  assume readdi.2: |- B e. CC


  assert |- ( B =/= 0 -> ( * ` ( A / B ) ) = ( ( * ` A ) / ( * ` B ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    ccj
    cfv
    cA
    ccj
    cfv
    cB
    ccj
    cfv
    cdiv
    co
    wceq
    recl.1
    readdi.2
    cA
    cB
    cjdiv
    mp3an12
end
