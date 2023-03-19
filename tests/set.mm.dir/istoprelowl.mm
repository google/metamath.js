include "ctb.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cr.mm"
include "ctopon.mm"
include "isbasisrelowl.mm"
include "cuni.mm"
include "tgtopon.mm"
include "icoreunrn.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "ax-mp.mm"

theorem istoprelowl
  let cI: class I
  assume istoprelowl.1: |- I = ( [,) " ( RR X. RR ) )


  assert |- ( topGen ` I ) e. ( TopOn ` RR )

  proof
    cI
    ctb
    wcel
    #
    cI
    ctg
    cfv
    #
    cr
    ctopon
    cfv
    #
    wcel
    cI
    istoprelowl.1
    isbasisrelowl
    @0
    @1
    cI
    cuni
    #
    ctopon
    cfv
    @2
    cI
    tgtopon
    @3
    cr
    ctopon
    cr
    @3
    cI
    istoprelowl.1
    icoreunrn
    eqcomi
    fveq2i
    syl6eleq
    ax-mp
end
