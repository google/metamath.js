include "c0.mm"
include "csn.mm"
include "cpw.mm"
include "cpr.mm"
include "cvv.mm"
include "pwpw0.mm"
include "p0ex.mm"
include "pwex.mm"
include "eqeltrri.mm"

theorem pp0ex



  assert |- { (/) , { (/) } } e. _V

  proof
    c0
    csn
    #
    cpw
    c0
    @0
    cpr
    cvv
    pwpw0
    @0
    p0ex
    pwex
    eqeltrri
end
