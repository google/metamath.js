include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absdiv.mm"
include "mp3an12.mm"

theorem absdivzi
  let cA: class A
  let cB: class B
  assume absvalsqi.1: |- A e. CC
  assume abssub.2: |- B e. CC


  assert |- ( B =/= 0 -> ( abs ` ( A / B ) ) = ( ( abs ` A ) / ( abs ` B ) ) )

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
    cabs
    cfv
    cA
    cabs
    cfv
    cB
    cabs
    cfv
    cdiv
    co
    wceq
    absvalsqi.1
    abssub.2
    cA
    cB
    absdiv
    mp3an12
end
