include "cr.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "crefld.mm"
include "cdr.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cv.mm"
include "recn.mm"
include "readdcl.mm"
include "renegcl.mm"
include "1re.mm"
include "remulcl.mm"
include "rereccl.mm"
include "cnsubdrglem.mm"
include "df-refld.mm"
include "eleq1i.mm"
include "anbi2i.mm"
include "mpbir.mm"

theorem resubdrg
  let vx: setvar x
  let vy: setvar y


  assert |- ( RR e. ( SubRing ` CCfld ) /\ RRfld e. DivRing )

  proof
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    crefld
    cdr
    wcel
    #
    wa
    @0
    ccnfld
    cr
    cress
    co
    #
    cdr
    wcel
    #
    wa
    vx
    vy
    cr
    vx
    cv
    #
    recn
    @4
    vy
    cv
    #
    readdcl
    @4
    renegcl
    1re
    @4
    @5
    remulcl
    @4
    rereccl
    cnsubdrglem
    @1
    @3
    @0
    crefld
    @2
    cdr
    df-refld
    eleq1i
    anbi2i
    mpbir
end
