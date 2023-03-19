include "csur.mm"
include "con0.mm"
include "cbday.mm"
include "wfo.mm"
include "wfun.mm"
include "bdayfo.mm"
include "fofun.mm"
include "ax-mp.mm"

theorem bdayfun



  assert |- Fun bday

  proof
    csur
    con0
    cbday
    wfo
    cbday
    wfun
    bdayfo
    csur
    con0
    cbday
    fofun
    ax-mp
end
