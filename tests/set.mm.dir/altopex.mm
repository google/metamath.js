include "caltop.mm"
include "csn.mm"
include "cpr.mm"
include "cvv.mm"
include "df-altop.mm"
include "prex.mm"
include "eqeltri.mm"

theorem altopex
  let cA: class A
  let cB: class B


  assert |- << A , B >> e. _V

  proof
    cA
    cB
    caltop
    cA
    csn
    #
    cA
    cB
    csn
    cpr
    #
    cpr
    cvv
    cA
    cB
    df-altop
    @0
    @1
    prex
    eqeltri
end
