include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "mulne0.mm"
include "mp4an.mm"

theorem mulne0i
  let cA: class A
  let cB: class B
  assume muln0.1: |- A e. CC
  assume muln0.2: |- B e. CC
  assume muln0.3: |- A =/= 0
  assume muln0.4: |- B =/= 0


  assert |- ( A x. B ) =/= 0

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    cB
    cc
    wcel
    cB
    cc0
    wne
    cA
    cB
    cmul
    co
    cc0
    wne
    muln0.1
    muln0.3
    muln0.2
    muln0.4
    cA
    cB
    mulne0
    mp4an
end
