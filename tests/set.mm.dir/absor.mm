include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cneg.mm"
include "0re.mm"
include "letric.mm"
include "mpan.mm"
include "absid.mm"
include "ex.mm"
include "absnid.mm"
include "orim12d.mm"
include "mpd.mm"

theorem absor
  let cA: class A


  assert |- ( A e. RR -> ( ( abs ` A ) = A \/ ( abs ` A ) = -u A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cc0
    cle
    wbr
    #
    wo
    #
    cA
    cabs
    cfv
    #
    cA
    wceq
    #
    @4
    cA
    cneg
    wceq
    #
    wo
    cc0
    cr
    wcel
    @0
    @3
    0re
    cc0
    cA
    letric
    mpan
    @0
    @1
    @5
    @2
    @6
    @0
    @1
    @5
    cA
    absid
    ex
    @0
    @2
    @6
    cA
    absnid
    ex
    orim12d
    mpd
end
