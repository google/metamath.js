include "csur.mm"
include "con0.mm"
include "cbday.mm"
include "wfo.mm"
include "crn.mm"
include "wceq.mm"
include "bdayfo.mm"
include "forn.mm"
include "ax-mp.mm"

theorem bdayrn



  assert |- ran bday = On

  proof
    csur
    con0
    cbday
    wfo
    cbday
    crn
    con0
    wceq
    bdayfo
    csur
    con0
    cbday
    forn
    ax-mp
end
