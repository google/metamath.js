include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "strfvn.mm"

theorem baseval
  let cK: class K
  assume baseval.k: |- K e. _V


  assert |- ( Base ` K ) = ( K ` 1 )

  proof
    cK
    cbs
    c1
    baseval.k
    df-base
    strfvn
end
