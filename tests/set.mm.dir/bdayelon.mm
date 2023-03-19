include "csur.mm"
include "con0.mm"
include "cbday.mm"
include "wfo.mm"
include "wf.mm"
include "bdayfo.mm"
include "fof.mm"
include "ax-mp.mm"
include "0elon.mm"
include "f0cli.mm"

theorem bdayelon
  let cA: class A


  assert |- ( bday ` A ) e. On

  proof
    csur
    con0
    cA
    cbday
    csur
    con0
    cbday
    wfo
    csur
    con0
    cbday
    wf
    bdayfo
    csur
    con0
    cbday
    fof
    ax-mp
    0elon
    f0cli
end
