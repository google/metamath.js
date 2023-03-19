include "csur.mm"
include "con0.mm"
include "cbday.mm"
include "wfo.mm"
include "wf.mm"
include "bdayfo.mm"
include "fof.mm"
include "ax-mp.mm"
include "fdmi.mm"

theorem bdaydm



  assert |- dom bday = No

  proof
    csur
    con0
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
    fdmi
end
