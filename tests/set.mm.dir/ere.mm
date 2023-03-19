include "ceu.mm"
include "c1.mm"
include "ce.mm"
include "cfv.mm"
include "cr.mm"
include "df-e.mm"
include "wcel.mm"
include "1re.mm"
include "reefcl.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem ere



  assert |- _e e. RR

  proof
    ceu
    c1
    ce
    cfv
    #
    cr
    df-e
    c1
    cr
    wcel
    @0
    cr
    wcel
    1re
    c1
    reefcl
    ax-mp
    eqeltri
end
