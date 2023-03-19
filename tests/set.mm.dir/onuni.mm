include "con0.mm"
include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "onss.mm"
include "ssonuni.mm"
include "mpd.mm"

theorem onuni
  let cA: class A


  assert |- ( A e. On -> U. A e. On )

  proof
    cA
    con0
    wcel
    cA
    con0
    wss
    cA
    cuni
    con0
    wcel
    cA
    onss
    cA
    con0
    ssonuni
    mpd
end
