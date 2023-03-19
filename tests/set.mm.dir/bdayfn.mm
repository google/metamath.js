include "csur.mm"
include "con0.mm"
include "cbday.mm"
include "wfo.mm"
include "wfn.mm"
include "bdayfo.mm"
include "fofn.mm"
include "ax-mp.mm"

theorem bdayfn



  assert |- bday Fn No

  proof
    csur
    con0
    cbday
    wfo
    cbday
    csur
    wfn
    bdayfo
    csur
    con0
    cbday
    fofn
    ax-mp
end
