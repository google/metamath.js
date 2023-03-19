include "c1p.mm"
include "cv.mm"
include "c1q.mm"
include "cltq.mm"
include "wbr.mm"
include "cab.mm"
include "cnp.mm"
include "df-1p.mm"
include "cnq.mm"
include "wcel.mm"
include "1nq.mm"
include "nqpr.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 1pr
  let vx: setvar x


  assert |- 1P e. P.

  proof
    c1p
    vx
    cv
    c1q
    cltq
    wbr
    vx
    cab
    #
    cnp
    vx
    df-1p
    c1q
    cnq
    wcel
    @0
    cnp
    wcel
    1nq
    vx
    c1q
    nqpr
    ax-mp
    eqeltri
end
