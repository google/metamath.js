include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "csigagen.mm"
include "cuni.mm"
include "csiga.mm"
include "cbrsiga.mm"
include "cr.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "sigagensiga.mm"
include "ax-mp.mm"
include "df-brsiga.mm"
include "uniretop.mm"
include "fveq2i.mm"
include "3eltr4i.mm"

theorem brsigarn



  assert |- BrSiga e. ( sigAlgebra ` RR )

  proof
    cioo
    crn
    #
    ctg
    cfv
    #
    csigagen
    cfv
    #
    @1
    cuni
    #
    csiga
    cfv
    #
    cbrsiga
    cr
    csiga
    cfv
    @1
    cvv
    wcel
    @2
    @4
    wcel
    @0
    ctg
    fvex
    @1
    cvv
    sigagensiga
    ax-mp
    df-brsiga
    cr
    @3
    csiga
    uniretop
    fveq2i
    3eltr4i
end
